"""Check SYNTHETIC policy fixtures against escalation_policy.decide and a reference selector.

The reference selector below exists only to check that the selector-contract data is
internally consistent. It is NOT part of escalation_policy.py and not the pipeline selector.
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from escalation_policy import decide  # noqa: E402


def combined(t, h, r):
    if any(v is None for v in (t, h, r)):
        return None
    return (t + h + r) / 3


def reference_select(case):
    b = case["baseline"]
    if b.get("verified", True) is False:
        return "BLOCKED_BASELINE"
    best_id, best = "ORIGINAL", combined(b["t"], b["h"], b["r"])
    for c in case["candidates"]:
        if not c.get("eligible") or c.get("versions_complete", True) is False:
            continue
        s = combined(c.get("t"), c.get("h"), c.get("r"))
        if s is not None and s > best:  # strict, raw values
            best_id, best = c["id"], s
    return best_id


def check_all(root):
    root = Path(root)
    ok = True
    rows = []
    for exp_path in sorted(root.rglob("*.expected.json")):
        inp = exp_path.with_name(exp_path.name.replace(".expected.json", ".json"))
        x = json.loads(inp.read_text(encoding="utf-8"))
        exp = json.loads(exp_path.read_text(encoding="utf-8"))
        assert x.get("synthetic") is True
        out = decide(x)
        good = out["action"] == exp["action"]
        if "scope" in exp:
            good &= out.get("scope") == exp["scope"]
        if "mode" in exp:
            good &= out.get("mode") == exp["mode"]
        if out.get("prompt"):
            good &= "SECRET_GOLD" not in out["prompt"]
            good &= out["api_called"] is False
        ok &= good
        rows.append((good, f"{exp_path.parent.name}/{inp.stem}", out["action"], out.get("scope"), exp["action"],
                     exp.get("scope")))
    for good, name, a, s, ea, es in rows:
        print(("PASS" if good else "FAIL"), name, f"got={a}/{s}", f"expected={ea}/{es}")
    for sel in root.rglob("selector_contract_cases.json"):
        data = json.loads(sel.read_text(encoding="utf-8"))
        for case in data["cases"]:
            got = reference_select(case)
            good = got == case["expected_winner"]
            ok &= good
            print(("PASS" if good else "FAIL"), "selector", case["id"], f"got={got}", f"expected={case['expected_winner']}")
    print("ALL PASS" if ok else "SOME FAILED")
    return ok


if __name__ == "__main__":
    sys.exit(0 if check_all(HERE / "policy-fixtures") else 1)
