"""Shared, lossless diagnostic normalization for CLI and REPL adapters.

Lean line numbers are 1-based and columns count Unicode characters from zero.
The original backend records are always retained; unavailable state stays None.
"""
import json
import re


def source_header_end(prefix):
    """Locate imports while ignoring strings and nested comments in fixed context."""
    masked, i, depth = list(prefix), 0, 0
    while i < len(prefix):
        if prefix.startswith("/-", i):
            depth += 1
            masked[i:i + 2] = "  "
            i += 2
        elif depth and prefix.startswith("-/", i):
            depth -= 1
            masked[i:i + 2] = "  "
            i += 2
        elif depth:
            masked[i] = "\n" if prefix[i] == "\n" else " "
            i += 1
        elif prefix.startswith("--", i):
            end = prefix.find("\n", i)
            end = len(prefix) if end < 0 else end
            masked[i:end] = " " * (end - i)
            i = end
        elif prefix[i] == '"':
            end = i + 1
            while end < len(prefix):
                if prefix[end] == "\\":
                    end += 2
                elif prefix[end] == '"':
                    end += 1
                    break
                else:
                    end += 1
            masked[i:end] = ["\n" if c == "\n" else " " for c in prefix[i:end]]
            i = end
        else:
            i += 1
    masked = "".join(masked)
    imports = list(re.finditer(r"^(?:(?:public|meta)\s+)*import\s+[^\n]+\n", masked, re.M))
    header = re.match(r"^(?:\s*(?:module|prelude)\b[^\n]*\n)+", masked)
    return imports[-1].end() if imports else (header.end() if header else 0)


def parse_cli_output(text):
    diagnostics, unparsed = [], []
    for line in text.splitlines():
        if not line.strip():
            continue
        try:
            raw = json.loads(line)
            if not isinstance(raw, dict) or "severity" not in raw:
                raise ValueError()
            diagnostics.append({"severity": raw.get("severity"), "position": raw.get("pos"),
                                "end_position": raw.get("endPos"), "message": raw.get("data"),
                                "source": "lean_cli", "raw": raw})
        except ValueError:
            unparsed.append(line)
    return diagnostics, unparsed


def is_unsolved(message):
    return bool(re.match(r"^unsolved goals(?:\s|$)", str(message)))


def classify_error_status(diagnostics):
    """Real proof errors take precedence when open goals accompany another error."""
    errors = [d for d in diagnostics if d.get("severity") == "error"]
    if not errors:
        return None
    return "incomplete" if all(is_unsolved(d.get("message")) for d in errors) else "proof_error"


def character_offset(text, position):
    if not isinstance(position, dict):
        return None
    line, column = position.get("line"), position.get("column")
    lines = text.splitlines(keepends=True)
    if type(line) is not int or type(column) is not int or not 1 <= line <= len(lines) or column < 0:
        return None
    return sum(map(len, lines[:line - 1])) + min(column, len(lines[line - 1].rstrip("\r\n")))


def source_position(text, offset):
    prefix = text[:offset]
    return {"line": prefix.count("\n") + 1, "column": len(prefix.rsplit("\n", 1)[-1])}


def enrich_diagnostics(diagnostics, text):
    """Attach exact original-source spans without replacing backend coordinates."""
    for diagnostic in diagnostics:
        first, last = (character_offset(text, diagnostic.get(key)) for key in ("position", "end_position"))
        if first is not None:
            diagnostic["source_line"] = text.splitlines()[diagnostic["position"]["line"] - 1]
            diagnostic["start_offset"] = first
            diagnostic["start_byte_offset"] = len(text[:first].encode())
        if last is not None:
            diagnostic["end_offset"] = last
            diagnostic["end_byte_offset"] = len(text[:last].encode())
        if first is not None and last is not None:
            diagnostic["source_text"] = text[first:last]
        match = re.search(r"has type\n(.*?)\nbut is expected to have type\n(.*?)(?:\nin the application|$)",
                          str(diagnostic.get("message")), re.S)
        if match:
            diagnostic["expected_actual_types"] = {"actual": match[1].strip(), "expected": match[2].strip()}
    return diagnostics


def split_states(states):
    """Split Lean's pretty-printed states while preserving multiline types/context."""
    goals, contexts = [], []
    for state in states:
        if not isinstance(state, str):
            continue
        for block in re.split(r"\n\s*\n(?=(?:case [^\n]*\n)?[^\n]*[:⊢])", state):
            marker = re.search(r"^(?:⊢|\|) ", block, re.M)
            if marker:  # `conv` tactic goals use the `|` marker.
                contexts.append(block[:marker.start()].rstrip())
                goals.append(block[marker.end():].strip())
    return goals or None, contexts or None


def map_info_records(records, text, inserted_bytes):
    """Undo diagnostic-only header/wrapper insertion, retaining backend raw data."""
    source = text.encode()
    result = []
    for raw in records:
        if not isinstance(raw, dict) or type(raw.get("start")) is not int or type(raw.get("end")) is not int:
            continue
        first, last = raw["start"] - inserted_bytes, raw["end"] - inserted_bytes
        if not 0 <= first <= last <= len(source):
            continue
        try:
            a, b = len(source[:first].decode()), len(source[:last].decode())
            token = source[first:last].decode()
        except UnicodeDecodeError:
            continue
        result.append({**raw, "raw": raw, "start": first, "end": last,
                       "start_offset": a, "end_offset": b,
                       "position": source_position(text, a), "end_position": source_position(text, b),
                       "source_text": token})
    return result


def apply_info_feedback(diagnostics, records):
    """Choose the smallest native tactic enclosing each error; never synthesize goals."""
    tactics = [r for r in records if r.get("kind") == "tactic"]
    first_goals = first_contexts = None
    for diagnostic in diagnostics:
        if diagnostic.get("severity") != "error":
            continue
        if is_unsolved(diagnostic.get("message")):
            goals, contexts = split_states([str(diagnostic["message"]).partition("\n")[2]])
            diagnostic.update(goals=goals, local_context=contexts, proof_state_source="unsolved_goals_diagnostic")
        else:
            offset = diagnostic.get("start_byte_offset")
            enclosing = [r for r in tactics if offset is not None and r["start"] <= offset < r["end"]]
            chosen = min(enclosing, key=lambda r: (r["end"] - r["start"], -r.get("depth", 0)), default=None)
            if chosen is None:
                diagnostic["context_unavailable_reason"] = "no native tactic InfoTree contains the error position"
                continue
            goals, contexts = split_states(chosen.get("goals_before", []))
            # An explicitly empty native state is known, rather than unavailable.
            if chosen.get("goals_before") == []:
                goals, contexts = [], []
            diagnostic.update(failed_tactic=chosen["source_text"],
                              tactic_range={key: chosen[key] for key in ("position", "end_position", "start_offset", "end_offset")},
                              goals=goals, local_context=contexts,
                              proof_state_source="lean_infotree_before_tactic", proof_state_raw=chosen["raw"])
        if first_goals is None and goals is not None:
            first_goals, first_contexts = goals, contexts
    sorries = [{"kind": "explicit_sorry", **{key: r[key] for key in (
        "position", "end_position", "start_offset", "end_offset", "source_text")}}
        for r in records if r.get("kind") == "explicit_sorry"]
    return first_goals, first_contexts, sorries
