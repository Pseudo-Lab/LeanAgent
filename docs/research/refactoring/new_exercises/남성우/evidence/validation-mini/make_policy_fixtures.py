#!/usr/bin/env python3
"""Generate SYNTHETIC policy fixtures P01..P04 (no Lean, no API).

Every file written here has "synthetic": true. Budgets, scores, metrics and
certificates are invented test inputs, NOT Lean measurements or price quotes.
Run: python3 make_policy_fixtures.py && python3 reproduce.py fixtures
"""
import copy
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from escalation_policy import digest  # noqa: E402

OUT = HERE / "policy-fixtures"

PREFIX = "def answer : Nat := 42\n\ntheorem answer_eq : answer = 42 := "
SUFFIX = "\n"
ORIGINAL = "by\n  rfl"
CANDIDATE = "by\n  simp [answer]\n  omega"
ENV = "synthetic-env-hash-A"


def base(candidate=CANDIDATE, status="invalid"):
    x = {
        "synthetic": True,
        "problem_id": "synthetic:answer_eq",
        "status": status,
        "baseline_verified": True,
        "environment": {"note": "synthetic fixture; no Lean run"},
        "environment_hash": ENV,
        "statement": "theorem answer_eq : answer = 42",
        "context": "def answer : Nat := 42",
        "original_proof": ORIGINAL,
        "candidate_proof": candidate,
        "candidate_hash": digest(candidate),
        "diagnostics": [{"kind": "synthetic", "message": "synthetic diagnostic: no goals to be proved"}],
        "localization": {"scope": "tactic", "trusted_pre_state": False},
        "local": {"state": "exhausted", "evidence": ["synthetic: fixed local list executed (not real)"]},
        "llm_history": [],
        "limits": {"repair_requests": 2, "optimization_requests": 1},
        "budget": {"cap_usd": 3.0, "spent_usd": 0.5, "reserved_usd": 0.0, "next_call_upper_bound_usd": 0.3},
        "constraints": ["Body only", "No sorry/admit/new axioms"],
        "gold_repair": "SECRET_GOLD_MUST_NOT_LEAK",
        "source_contract": {"original_source": PREFIX + ORIGINAL + SUFFIX,
                            "candidate_source": PREFIX + candidate + SUFFIX,
                            "body_start": len(PREFIX), "body_end": len(PREFIX) + len(ORIGINAL)},
    }
    return x


def cert(x, **over):
    c = {"candidate_hash": digest(x["candidate_proof"]), "environment_hash": x["environment_hash"],
         "capture": "before_failed_tactic", "prefix_replayed": True, "prefix_error_count": 0,
         "recovery_used": False, "contains_sorry": False,
         "state_digest": "synthetic-state-1", "replayed_state_digest": "synthetic-state-1"}
    c.update(over)
    return c


def metrics(x, **over):
    m = {"baseline_tokens": 100, "baseline_heartbeats": 1000, "candidate_tokens": 80,
         "candidate_heartbeats": 700, "versions_passed": 3, "versions_total": 3,
         "incumbent_score": 100 / 3, "all_versions_checked": True,
         "candidate_hash": digest(x["candidate_proof"]), "environment_hash": x["environment_hash"],
         "comparable_to_incumbent": True, "measurement_kind": "synthetic"}
    m.update(over)
    return m


FIX = {}  # path -> (input, expected)


def add(bundle, name, x, action, scope=None, mode=None, note=""):
    exp = {"action": action, "note": note}
    if scope is not None:
        exp["scope"] = scope
    if mode is not None:
        exp["mode"] = mode
    FIX[(bundle, name)] = (x, exp)


# ---------------------------------------------------------------- P01 budget / price
B = "P01"
x = base(); x["budget"] = {"cap_usd": 1.0, "spent_usd": 0.8, "reserved_usd": 0.0, "next_call_upper_bound_usd": 0.3}
add(B, "a_insufficient_budget", x, "SELECT_BEST", note="0.8+0+0.3 > 1.0: no prompt, incumbent kept")
x = base(); x["budget"]["reserved_usd"] = 2.3
add(B, "b_parallel_reservation_exhausts_cap", x, "SELECT_BEST", note="0.5+2.3+0.3 > 3.0 because of a reservation")
x = base(); x["budget"]["next_call_upper_bound_usd"] = None
add(B, "c_price_unknown", x, "PRICE_REQUEST", note="no conservative upper bound -> ask for price, never guess")
x = base(); x["budget"]["cap_usd"] = None
add(B, "d_cap_unknown", x, "PRICE_REQUEST")
x = base(); x["budget"]["next_call_upper_bound_usd"] = -0.1
add(B, "e_negative_bound", x, "PRICE_REQUEST")
x = base(); x["budget"] = {"cap_usd": 1.0, "spent_usd": 0.7, "reserved_usd": 0.0, "next_call_upper_bound_usd": 0.3}
add(B, "f_exactly_fits_cap", x, "EMIT_LLM_PROMPT", scope="body", mode="repair",
    note="0.7+0+0.3 == 1.0 is allowed (<=); no certificate -> body scope")

# ---------------------------------------------------------------- P02 duplicate / scope widening
B = "P02"
x = base(); x["duplicate_request"] = True
add(B, "a_identical_request_repeated", x, "REUSE_OR_STOP",
    note="same proof hash, env hash, diagnostics, scope and context already sent")
x = base(); x["duplicate_request"] = False
x["diagnostics"] = [{"kind": "synthetic", "message": "NEW diagnostic after need_context was served"}]
x["llm_history"] = [{"mode": "repair", "scope": "body", "same_failure": False, "candidate_hash": x["candidate_hash"]}]
add(B, "b_same_candidate_new_information_not_blocked", x, "EMIT_LLM_PROMPT", scope="body", mode="repair",
    note="candidate hash equal to a previous request but new context -> not a duplicate")
x = base(); x["localization"] = {"scope": "tactic"}; x["state_certificate"] = cert(x)
add(B, "c_first_request_tactic_with_certificate", x, "EMIT_LLM_PROMPT", scope="tactic", mode="repair")
x = base(); x["localization"] = {"scope": "tactic"}; x["state_certificate"] = cert(x)
x["llm_history"] = [{"mode": "repair", "scope": "tactic", "same_failure": True}]
add(B, "d_same_failure_widens_tactic_to_block", x, "EMIT_LLM_PROMPT", scope="block", mode="repair")
x = base(); x["localization"] = {"scope": "tactic"}; x["state_certificate"] = cert(x)
x["llm_history"] = [{"mode": "repair", "scope": "block", "same_failure": True}]
x["limits"]["repair_requests"] = 3
add(B, "e_same_failure_widens_block_to_body", x, "EMIT_LLM_PROMPT", scope="body", mode="repair")
x = base()
x["llm_history"] = [{"mode": "repair", "scope": "body", "same_failure": True},
                    {"mode": "repair", "scope": "body", "same_failure": True}]
add(B, "f_repair_limit_reached", x, "SELECT_BEST", note="2 repair requests already used; stop, keep incumbent")
x = base(); x["local"] = {"state": "pending", "evidence": ["synthetic: simp? not yet run"]}
add(B, "g_local_pending", x, "RUN_LOCAL")
x = base(); x["local"] = {"state": "exhausted", "evidence": []}
add(B, "h_local_without_evidence", x, "COLLECT_EVIDENCE")

# ---------------------------------------------------------------- P03 environment / baseline / contract
B = "P03"
x = base(); x["status"] = "environment_error"
x["diagnostics"] = [{"kind": "synthetic", "message": "unknown package 'Mathlib' (setup failure)"}]
add(B, "a_environment_error", x, "FIX_ENVIRONMENT", note="never a proof-repair request")
x = base(); x["baseline_verified"] = False
add(B, "b_baseline_unverified", x, "VERIFY_BASELINE", note="fallback to an unverified original is NOT a normal success")
x = base(); x["status"] = "input_error"
add(B, "c_wrapper_parse_error", x, "REJECT_CANDIDATE")
# statement / answer changed: answer = 42 -> answer = 43 (body unchanged-looking)
x = base(candidate=ORIGINAL)
x["source_contract"]["candidate_source"] = PREFIX.replace("answer = 42", "answer = 43") + ORIGINAL + SUFFIX
add(B, "d_answer_changed_42_to_43", x, "REJECT_CANDIDATE", note="conclusion value changed outside body")
x = base(candidate=ORIGINAL)
x["source_contract"]["candidate_source"] = (PREFIX.replace("theorem answer_eq :", "theorem answer_eq (h : False) :")
                                            + ORIGINAL + SUFFIX)
add(B, "e_hypothesis_added", x, "REJECT_CANDIDATE", note="extra hypothesis outside body")
x = base()
x["source_contract"]["candidate_source"] = PREFIX.replace("def answer", "def  answer") + CANDIDATE + SUFFIX
add(B, "f_whitespace_change_outside_body", x, "REJECT_CANDIDATE", note="even whitespace outside body is rejected")
x = base()
x["source_contract"]["candidate_source"] = PREFIX + CANDIDATE + "\ntheorem extra : True := trivial\n"
add(B, "g_suffix_declaration_appended", x, "REJECT_CANDIDATE")
x = base(); del x["source_contract"]
add(B, "h_contract_missing", x, "CHECK_CONTRACT")
x = base(); x["source_contract"]["body_end"] = x["source_contract"]["body_start"] + 3
add(B, "i_body_range_inconsistent", x, "REJECT_CANDIDATE", note="source[a:b] != original_proof")
x = base(); x["contract_violation"] = True
add(B, "j_runner_flagged_violation", x, "REJECT_CANDIDATE")
# certificate integrity
x = base(); x["localization"] = {"scope": "tactic"}
x["state_certificate"] = cert(x, candidate_hash=digest("by\n  simp"))
add(B, "k_stale_candidate_certificate", x, "EMIT_LLM_PROMPT", scope="body", mode="repair",
    note="certificate for an older body -> state not trusted -> body scope")
x = base(); x["localization"] = {"scope": "tactic"}
x["state_certificate"] = cert(x, environment_hash="synthetic-env-hash-OLD")
add(B, "l_stale_environment_certificate", x, "EMIT_LLM_PROMPT", scope="body", mode="repair")
x = base(); x["localization"] = {"scope": "tactic", "trusted_pre_state": True}
add(B, "m_trusted_pre_state_flag_without_certificate", x, "EMIT_LLM_PROMPT", scope="body", mode="repair",
    note="the legacy boolean flag alone must not narrow the scope")
x = base(); x["localization"] = {"scope": "tactic"}
x["state_certificate"] = cert(x, recovery_used=True)
add(B, "n_certificate_with_error_recovery", x, "EMIT_LLM_PROMPT", scope="body", mode="repair")
x = base(); x["localization"] = {"scope": "tactic"}
x["state_certificate"] = cert(x, replayed_state_digest="synthetic-state-2")
add(B, "o_certificate_digest_mismatch", x, "EMIT_LLM_PROMPT", scope="body", mode="repair")
x = base(); x["localization"] = {"scope": "tactic"}
x["state_certificate"] = cert(x, prefix_error_count=1)
add(B, "p_certificate_prefix_errors", x, "EMIT_LLM_PROMPT", scope="body", mode="repair")

# ---------------------------------------------------------------- P04 metrics / optimization gate
B = "P04"
V = "by\n  decide"


def valid(**mover):
    x = base(candidate=V, status="valid")
    x["diagnostics"] = []
    x["local"] = {"state": "exhausted", "evidence": ["synthetic: simp?/aesop? extraction attempted (not real)"]}
    x["metrics"] = metrics(x, **mover)
    return x


add(B, "a_tie_with_original", valid(candidate_tokens=100, candidate_heartbeats=1000), "EMIT_LLM_PROMPT",
    scope="body", mode="optimization", note="score 33.33 <= incumbent 33.33 -> optimization request")
add(B, "b_clear_improvement", valid(), "SELECT_BEST", note="score 50 > 33.33, HB 70%, all versions: no trigger")
add(B, "c_shorter_but_heartbeat_125pct", valid(candidate_tokens=40, candidate_heartbeats=1250), "EMIT_LLM_PROMPT",
    scope="body", mode="optimization", note="score 36.67 > incumbent but HB >= 125% baseline")
add(B, "d_version_failure", valid(versions_passed=2), "EMIT_LLM_PROMPT", scope="body", mode="optimization")
x = valid(); del x["metrics"]["candidate_heartbeats"]
add(B, "e_heartbeat_missing", x, "MEASURE")
add(B, "f_versions_not_all_checked", valid(all_versions_checked=False), "MEASURE")
add(B, "g_stale_metric_hash", valid(candidate_hash=digest("by\n  rfl")), "MEASURE")
add(B, "h_baseline_tokens_zero", valid(baseline_tokens=0), "MEASURE", note="special denominator unsupported")
add(B, "i_not_comparable_to_incumbent", valid(comparable_to_incumbent=False), "MEASURE")
x = valid(); x["metrics"]["candidate_heartbeats"] = float("nan")
add(B, "j_nan_metric", x, "MEASURE")
x = valid(); del x["metrics"]
x["optimization_evidence"] = "uses aesop, probably expensive"
add(B, "k_narrative_evidence_only", x, "MEASURE", note="free text never triggers optimization")
x = valid(candidate_tokens=100, candidate_heartbeats=1000)
x["llm_history"] = [{"mode": "optimization", "scope": "body", "result": "model returned invalid body"}]
add(B, "l_model_failed_limit_reached", x, "SELECT_BEST",
    note="optimization limit used; selector must keep the best verified incumbent")
x = valid(candidate_tokens=100, candidate_heartbeats=1000)
x["budget"]["next_call_upper_bound_usd"] = None
add(B, "m_trigger_but_price_unknown", x, "PRICE_REQUEST")

# ---------------------------------------------------------------- selector contract (NOT implemented by policy)
SELECTOR = [
    {"id": "s01_table_from_design_doc", "baseline": {"t": 0, "h": 0, "r": 100},
     "candidates": [
         {"id": "very_short_expensive", "eligible": True, "t": 40, "h": -80, "r": 100},
         {"id": "balanced", "eligible": True, "t": 20, "h": 30, "r": 100},
         {"id": "shorter_version_loss", "eligible": True, "t": 50, "h": 10, "r": 200 / 3},
         {"id": "best_combined", "eligible": True, "t": 10, "h": 50, "r": 100},
         {"id": "fake_high_invalid", "eligible": False, "t": 90, "h": 90, "r": 100}],
     "expected_winner": "best_combined"},
    {"id": "s02_tie_with_baseline", "baseline": {"t": 0, "h": 0, "r": 100},
     "candidates": [{"id": "tie", "eligible": True, "t": 10, "h": -10, "r": 100}],
     "expected_winner": "ORIGINAL", "note": "equal combined -> keep verified original"},
    {"id": "s03_all_worse", "baseline": {"t": 0, "h": 0, "r": 100},
     "candidates": [{"id": "w1", "eligible": True, "t": 5, "h": -20, "r": 100}],
     "expected_winner": "ORIGINAL"},
    {"id": "s04_display_rounding_tie", "baseline": {"t": 0, "h": 0, "r": 100},
     "candidates": [{"id": "a", "eligible": True, "t": 10.0001, "h": 0, "r": 100},
                    {"id": "b", "eligible": True, "t": 10.0002, "h": 0, "r": 100}],
     "expected_winner": "b", "note": "both display as 36.67; compare raw values"},
    {"id": "s05_high_score_but_hb_missing", "baseline": {"t": 0, "h": 0, "r": 100},
     "candidates": [{"id": "no_hb", "eligible": True, "t": 60, "h": None, "r": 100},
                    {"id": "ok", "eligible": True, "t": 5, "h": 5, "r": 100}],
     "expected_winner": "ok", "note": "incomplete metrics are not comparable"},
    {"id": "s06_partial_robustness_unchecked", "baseline": {"t": 0, "h": 0, "r": 100},
     "candidates": [{"id": "partial", "eligible": True, "t": 30, "h": 30, "r": 100, "versions_complete": False}],
     "expected_winner": "ORIGINAL"},
    {"id": "s07_no_candidates", "baseline": {"t": 0, "h": 0, "r": 100}, "candidates": [],
     "expected_winner": "ORIGINAL"},
    {"id": "s08_all_invalid", "baseline": {"t": 0, "h": 0, "r": 100},
     "candidates": [{"id": "x", "eligible": False, "t": 50, "h": 50, "r": 100}], "expected_winner": "ORIGINAL"},
    {"id": "s09_baseline_unverified", "baseline": {"t": 0, "h": 0, "r": 100, "verified": False},
     "candidates": [{"id": "x", "eligible": True, "t": 10, "h": 10, "r": 100}],
     "expected_winner": "BLOCKED_BASELINE", "note": "not a normal fallback success"},
    {"id": "s10_model_failure_after_best", "baseline": {"t": 0, "h": 0, "r": 100},
     "candidates": [{"id": "local_best", "eligible": True, "t": 20, "h": 20, "r": 100},
                    {"id": "model_opt_failed", "eligible": False, "t": 70, "h": 70, "r": 100},
                    {"id": "model_no_response", "eligible": False, "t": None, "h": None, "r": None}],
     "expected_winner": "local_best", "note": "existing best preserved after later failures"},
    {"id": "s11_one_axis_worse_still_wins", "baseline": {"t": 0, "h": 0, "r": 100},
     "candidates": [{"id": "hb_worse", "eligible": True, "t": 60, "h": -10, "r": 100},
                    {"id": "t_only", "eligible": True, "t": 15, "h": 0, "r": 100}],
     "expected_winner": "hb_worse", "note": "do not reject on one-axis regression; do not pick on one axis"},
    {"id": "s12_baseline_robustness_partial", "baseline": {"t": 0, "h": 0, "r": 200 / 3},
     "candidates": [{"id": "fixes_version", "eligible": True, "t": 0, "h": 0, "r": 100}],
     "expected_winner": "fixes_version", "note": "baseline combined is 22.22, not 33.33 and not 0"},
]


def main():
    if OUT.exists():
        for p in sorted(OUT.rglob("*"), reverse=True):
            if p.is_file():
                p.unlink()
    for (bundle, name), (x, exp) in FIX.items():
        d = OUT / bundle
        d.mkdir(parents=True, exist_ok=True)
        (d / f"{name}.json").write_text(json.dumps(x, ensure_ascii=False, indent=2, allow_nan=True) + "\n",
                                        encoding="utf-8")
        (d / f"{name}.expected.json").write_text(json.dumps({"synthetic": True, **exp}, ensure_ascii=False,
                                                            indent=2) + "\n", encoding="utf-8")
    sel = {"synthetic": True,
           "note": "escalation_policy.py does NOT implement a score selector. These cases test a separate "
                   "selector contract (combined = mean of token reduction %, HB reduction %, robustness %). "
                   "Values are invented; they are not Lean measurements.",
           "cases": SELECTOR}
    (OUT / "P04" / "selector_contract_cases.json").write_text(
        json.dumps(sel, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {len(FIX)} policy inputs and {len(SELECTOR)} selector cases")


if __name__ == "__main__":
    main()
