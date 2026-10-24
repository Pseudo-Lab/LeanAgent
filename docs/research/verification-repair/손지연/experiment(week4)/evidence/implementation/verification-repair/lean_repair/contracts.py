"""The backend-independent contract; source offsets are Unicode character offsets."""
from dataclasses import asdict, dataclass, field
from hashlib import sha256
import json
import math
from pathlib import Path
import re
from typing import Protocol


class TaskConfigurationError(ValueError):
    stop_reason = "config_error"


class StatementMismatch(TaskConfigurationError):
    """The fixed theorem, its context, or its declared identity changed."""
    stop_reason = "statement_mismatch"


class EnvironmentMismatch(TaskConfigurationError):
    stop_reason = "environment_error"


def digest(text: str | bytes) -> str:
    return sha256(text.encode() if isinstance(text, str) else text).hexdigest()


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def declaration_name(text: str, start: int, body_start: int) -> str:
    """Bind ordinary namespace/lemma syntax to the audited target, excluding comments."""
    visible, i, depth = list(text[:body_start]), 0, 0
    while i < body_start:
        if text.startswith("/-", i):
            depth += 1
            visible[i:i+2] = "  "
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            visible[i:i+2] = "  "
            i += 2
        elif depth:
            visible[i] = "\n" if text[i] == "\n" else " "
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i, body_start)
            end = body_start if end < 0 else end
            visible[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            visible[i] = " "
            i += 1
            while i < body_start:
                char = text[i]
                visible[i] = "\n" if char == "\n" else " "
                i += 1
                if char == "\\" and i < body_start:
                    visible[i] = " "
                    i += 1
                elif char == '"':
                    break
        else:
            i += 1
    visible = "".join(visible)
    current, stack = "", []
    for match in re.finditer(r"^[ \t]*(?:(?:meta|noncomputable)\s+)?(namespace|section|end)\b(?:[ \t]+([\w'.]+))?", visible[:start], re.M):
        command, name = match.groups()
        if command == "end":
            if stack:
                current = stack.pop()
        else:
            stack.append(current)
            if command == "namespace":
                if not name:
                    raise ValueError("namespace must have an ordinary identifier")
                current = name[7:] if name.startswith("_root_.") else ".".join(filter(None, (current, name)))
    declarations = list(re.finditer(r"\b(?:theorem|lemma)\s+([\w'.]+)(?=\s|[:({])", visible[start:body_start]))
    if len(declarations) != 1:
        raise ValueError("editable span must belong to one ordinary theorem or lemma command")
    name = declarations[0][1]
    return name[7:] if name.startswith("_root_.") else ".".join(filter(None, (current, name)))


@dataclass
class VerificationResult:
    task_id: str
    attempt: str
    candidate_hash: str
    environment_id: str
    check_kind: str
    status: str
    process_exit_code: int | None = None
    diagnostics: list = field(default_factory=list)
    goals: list | None = None
    local_context: list | None = None
    sorries: list | None = None
    backend_proof_status: str | None = None
    statement_check: str = "not_run"
    axioms: list | None = None
    metrics: dict = field(default_factory=dict)
    elapsed_ms: int = 0
    raw_log_path: str | None = None
    detail: str | None = None
    failure_kind: str | None = None

    def to_dict(self):
        return asdict(self)


@dataclass
class TaskSpec:
    config: dict
    source: Path
    project: Path
    text: str
    declaration_start: int
    body_start: int
    body_end: int
    reference_text: str | None = None
    reference_source: Path | None = None

    @classmethod
    def load(cls, filename: str | Path):
        filename = Path(filename).resolve()
        config = json.loads(filename.read_text())
        if not isinstance(config, dict):
            raise TaskConfigurationError("task configuration must be a JSON object")
        for key in ("pins", "span"):
            if not isinstance(config.get(key), dict):
                raise TaskConfigurationError(f"{key} must be a JSON object")
        for key in ("limits", "model", "backend"):
            if key in config and not isinstance(config[key], dict):
                raise TaskConfigurationError(f"{key} must be a JSON object")
        for key in ("source", "project", "target"):
            if not isinstance(config.get(key), str) or not config[key].strip():
                raise TaskConfigurationError(f"{key} must be a nonempty string")
        if not isinstance(config["pins"].get("toolchain"), str) or not config["pins"]["toolchain"].strip():
            raise TaskConfigurationError("pins.toolchain must be a nonempty string")
        if "allowed_axioms" in config and (not isinstance(config["allowed_axioms"], list)
                or not all(isinstance(name, str) and re.fullmatch(r"[\w'.]+", name) for name in config["allowed_axioms"])):
            raise TaskConfigurationError("allowed_axioms must be a list of Lean declaration names")
        if config.get("reference") is not None and not isinstance(config["reference"], str):
            raise TaskConfigurationError("reference must be a path string")
        fixed = config["pins"].get("fixed_context")
        if fixed is not None and (not isinstance(fixed, dict)
                or any(type(fixed.get(key)) is not int or fixed[key] < 0 for key in ("prefix_chars", "suffix_chars"))
                or any(not isinstance(fixed.get(key), str) for key in ("prefix_sha256", "suffix_sha256"))):
            raise TaskConfigurationError("invalid fixed context pins")
        if not isinstance(config.get("task_id"), str) or not config["task_id"].strip():
            raise ValueError("task_id must be a nonempty stable problem identifier")
        path = lambda name: (filename.parent / config[name]).resolve()
        source, project = path("source"), path("project")
        text = source.read_text()
        if digest(source.read_bytes()) != config["pins"]["source_sha256"]:
            fixed = config["pins"].get("fixed_context")
            if fixed:
                prefix, suffix = text[:fixed["prefix_chars"]], text[len(text)-fixed["suffix_chars"]:] if fixed["suffix_chars"] else ""
                if digest(prefix) != fixed["prefix_sha256"] or digest(suffix) != fixed["suffix_sha256"]:
                    raise StatementMismatch("source SHA256 mismatch: fixed theorem/context changed")
            raise EnvironmentMismatch("source SHA256 mismatch; regenerate the task after intentional edits")
        if not re.fullmatch(r"[\w'.]+", config["target"], re.UNICODE):
            raise ValueError("target must be a fully qualified ordinary Lean declaration name")
        span = config["span"]
        a, b, c = (span[k] for k in ("declaration_start", "body_start", "body_end"))
        if not all(type(x) is int for x in (a, b, c)) or not 0 <= a < b < c <= len(text):
            raise ValueError("invalid source character span")
        if not text[b:c].startswith("by"):
            raise ValueError("only a complete by proof body is editable")
        if text[c:] and not text[c:].lstrip(" \t").startswith(("\n", "\r")):
            raise ValueError("fixed suffix must retain the newline separating later commands; regenerate task")
        if declaration_name(text, a, b) != config["target"]:
            raise StatementMismatch("target does not match the declaration and namespace at the editable span")
        if fixed and (fixed["prefix_chars"] != b or fixed["suffix_chars"] != len(text)-c
                      or fixed["prefix_sha256"] != digest(text[:b])
                      or fixed["suffix_sha256"] != digest(text[c:])):
            raise TaskConfigurationError("fixed context pins do not match the configured proof span")
        reference, reference_source = None, None
        if config.get("reference"):
            reference_source = path("reference")
            raw = reference_source.read_bytes()
            if digest(raw) != config["pins"].get("reference_sha256"):
                raise ValueError("reference SHA256 mismatch")
            reference = raw.decode()
            if not reference.startswith(text[:b]) or not reference.endswith(text[c:]):
                raise ValueError("reference must have the exact same fixed prefix and suffix")
        limits = config.setdefault("limits", {})
        for key, default in {"repair_calls": 3, "lean_seconds": 300, "model_seconds": 300,
                             "task_seconds": 1800, "setup_seconds": 600,
                             "max_heartbeats": 200000, "infra_retries": 1}.items():
            limits.setdefault(key, default)
            if type(limits[key]) not in (int, float) or not math.isfinite(limits[key]) or limits[key] <= 0:
                raise ValueError(f"{key} must be positive")
        if type(limits["repair_calls"]) is not int or not 1 <= limits["repair_calls"] <= 3:
            raise ValueError("repair_calls must be 1..3")
        if type(limits["infra_retries"]) is not int or type(limits["max_heartbeats"]) is not int:
            raise ValueError("infra_retries and max_heartbeats must be integers")
        for key in ("proof_tokens", "heartbeats", "model_tokens"):
            if limits.get(key) is not None and (type(limits[key]) is not int or limits[key] <= 0):
                raise ValueError(f"{key} must be a positive integer or null")
        return cls(config, source, project, text, a, b, c, reference, reference_source)

    def assert_statement(self, actual_text: str | None = None) -> None:
        """Fatal drift is distinct from a repairable error inside the proof body."""
        if declaration_name(self.text, self.declaration_start, self.body_start) != self.config["target"]:
            raise StatementMismatch("target declaration identity changed")
        actual = self.source.read_text() if actual_text is None else actual_text
        prefix, suffix = self.text[:self.body_start], self.text[self.body_end:]
        if (len(actual) < len(prefix) + len(suffix) or not actual.startswith(prefix)
                or suffix and not actual.endswith(suffix)):
            raise StatementMismatch("fixed theorem, assumptions, imports or surrounding definitions changed")

    @property
    def task_id(self):
        return self.config["task_id"]

    @property
    def limits(self):
        return self.config["limits"]

    @property
    def initial_body(self):
        return self.text[self.body_start:self.body_end]

    def body_from(self, text):
        suffix = self.text[self.body_end:]
        return text[self.body_start:len(text) - len(suffix) if suffix else len(text)]

    def assemble(self, body):
        return self.text[:self.body_start] + body + self.text[self.body_end:]


class Verifier(Protocol):
    """Implement this contract to replace the CLI backend with REPL/LSP."""
    def prepare(self) -> VerificationResult: ...
    def verify(self, body: str, attempt: str, check_kind: str = "candidate") -> VerificationResult: ...


class RepairPolicy(Protocol):
    def propose(self, request: dict, directory: Path, timeout: float, budget) -> dict: ...
