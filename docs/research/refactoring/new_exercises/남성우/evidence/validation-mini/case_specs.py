"""Case definitions for validation-mini R01..R08.

Each case = fixed original declaration + ONE realistic refactor mutation (edits applied to
the original body) + an independently written gold repair (alternatives tried in order;
all attempts are logged). Gold bodies and expectations are never put into request.json.

`prediction` is the author's guess written BEFORE running Lean. Labels in case.json come
from the observed Lean results, not from this field.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
_SEEDS = [json.loads(l) for l in (HERE / "sources/warmup_seeds_1_3.jsonl").read_text(encoding="utf-8").splitlines()]
S1, S2, S3 = _SEEDS  # warm-up lines 1, 2, 3 of benchmark_data_warmup.jsonl


def strata(seed, line_no, source, full_name):
    return dict(
        seed_id=f"warmup-{line_no}:{seed['name']}", source_kind="arena_derived", project="strata",
        source=source, statement=seed["statement"], decl_src=seed["src"], full_name=full_name,
        source_origin=f"benchmark_data_warmup.jsonl line {line_no}; {seed['file_path']} @ "
                      f"{list(seed['version_info'][-1].values())[0][:9]} (git HEAD copy, uncommitted patch excluded)",
        listed_versions=[list(v.keys())[0] for v in seed["version_info"]],
        available_versions=["v4.26.0"],
    )


def toy(path, statement, body, full_name):
    return dict(
        seed_id=f"toy:{full_name}", source_kind="toy", project="mathlib_toy", source=path,
        statement=statement, decl_src=statement + " := " + body, full_name=full_name,
        source_origin=f"validation-mini/{path} (educational example written for this dataset)",
        listed_versions=[], available_versions=["mathlib_toy pinned env only"],
        version_note="toy example: no Arena version list; robustness not applicable/not complete",
    )


CE = "sources/strata_CallElimCorrect_HEAD.lean"
SSP = "sources/strata_StatementSemanticsProps_HEAD.lean"

CASES = {}

# R01 projection chosen in the wrong order --------------------------------------------
CASES["R01"] = toy(
    "sources/toy/R01_and_swap.lean",
    "theorem r01_and_swap (P Q R : Prop) (h : (P ∧ Q) ∧ R) : R ∧ P",
    "by\n  constructor\n  · exact h.2\n  · exact h.1.1",
    "ValidationMini.r01_and_swap",
) | dict(
    mutation=[("constructor\n  · exact h.2\n  · exact h.1.1", "exact ⟨h.1.1, h.2⟩")],
    expected_intent="Collapse the two constructor branches into one anonymous-constructor term; the refactorer "
                    "listed the projections in hypothesis order (P first) instead of goal order (R first).",
    gold_alternatives=[[("exact ⟨h.1.1, h.2⟩", "exact ⟨h.2, h.1.1⟩")]],
    gold_strategy="intent preserved: single anonymous-constructor term with projections in goal order",
    prediction="type mismatch at the exact line; local simp_all or exact? likely closes it (no LLM)",
)

# R02 re-introducing an existing binder -------------------------------------------------
CASES["R02"] = strata(S2, 2, CE, "CallElimCorrect.extractedOldExprInVars") | dict(
    mutation=[("  intros Hnorm\n", "  intro post Hnorm\n")],
    expected_intent="Refactorer believed the auto-bound implicit `post` must be introduced before the hypothesis "
                    "and rewrote `intros Hnorm` as `intro post Hnorm` (post is already a binder of the statement).",
    gold_alternatives=[[("  intro post Hnorm\n", "  intro Hnorm\n")]],
    gold_strategy="keeps the switch from `intros` to `intro`, drops the spurious `post` name",
    prediction="error at the intro line; delete_span loses Hnorm so later `cases Hnorm` fails -> escalate (body)",
)

# R03 simp -> simp only with a dropped rule ---------------------------------------------
CASES["R03"] = strata(S2, 2, CE, "CallElimCorrect.extractedOldExprInVars") | dict(
    mutation=[("simp [Imperative.HasVarsPure.getVars, extractOldExprVars,\n          Lambda.LExpr.LExpr.getVars] at *",
               "simp only [Imperative.HasVarsPure.getVars, extractOldExprVars] at *")],
    expected_intent="Make the broad initial simp explicit (`simp only`) for robustness, but forget "
                    "`Lambda.LExpr.LExpr.getVars` and the default simp set lemmas it relied on.",
    gold_alternatives=[
        [("simp only [Imperative.HasVarsPure.getVars, extractOldExprVars] at *",
          "simp only [Imperative.HasVarsPure.getVars, extractOldExprVars,\n          Lambda.LExpr.LExpr.getVars] at *")],
        [("simp only [Imperative.HasVarsPure.getVars, extractOldExprVars] at *",
          "simp [Imperative.HasVarsPure.getVars, extractOldExprVars,\n          Lambda.LExpr.LExpr.getVars] at *")],
    ],
    gold_strategy="first try: simp only with the dropped rule restored (intent kept); fallback: original simp restored",
    prediction="the `<;> try simp_all` may hide part of it; a later case probably fails with unsolved goals",
)

# R04 aesop refactor; explicit script extraction (valid path) ----------------------------
CASES["R04"] = toy(
    "sources/toy/R04_inter_union.lean",
    "theorem r04_inter_union {α : Type*} (s t u : Set α) (x : α) (hx : x ∈ s ∩ (t ∪ u)) :\n    x ∈ (s ∩ t) ∪ (s ∩ u)",
    "by\n  obtain ⟨hs, htu⟩ := hx\n  rcases htu with ht | hu\n  · exact Or.inl ⟨hs, ht⟩\n  · exact Or.inr ⟨hs, hu⟩",
    "ValidationMini.r04_inter_union",
) | dict(
    mutation=[("obtain ⟨hs, htu⟩ := hx\n  rcases htu with ht | hu\n  · exact Or.inl ⟨hs, ht⟩\n  · exact Or.inr ⟨hs, hu⟩",
               "aesop")],
    expected_intent="Shorten the explicit case split to a single `aesop` call (expected valid; the question is "
                    "whether the raw call or the extracted aesop? script is cheaper).",
    gold_alternatives=[[]],
    gold_strategy="candidate itself is the reference if valid (no repair needed)",
    prediction="valid; aesop? yields a script; HB comparison unknown before measuring",
)

# R05 premature `left` -------------------------------------------------------------------
CASES["R05"] = toy(
    "sources/toy/R05_mem_cons.lean",
    "theorem r05_mem_cons (x a : ℕ) (l : List ℕ) (h : x ∈ l) : x ∈ a :: l",
    "by\n  simp only [List.mem_cons]\n  right\n  exact h",
    "ValidationMini.r05_mem_cons",
) | dict(
    mutation=[("  right\n", "  left\n")],
    expected_intent="While reordering the disjunction proof the refactorer committed to the first disjunct "
                    "(`left`) too early; the remaining tactic is fine for the other branch only.",
    gold_alternatives=[[("  left\n  exact h", "  exact Or.inr h")]],
    gold_strategy="keeps the single explicit-term style, chooses the correct disjunct",
    prediction="type mismatch at `exact h`; ops only touch that line so they fail -> escalate",
    inferred_state="(human inference, NOT trusted) after `left`: goal `x = a` with `h : x ∈ l`, unprovable",
)

# R06 induction context lost --------------------------------------------------------------
CASES["R06"] = strata(S3, 3, SSP, "Core.InitsUpdatesComm") | dict(
    mutation=[("induction Hup generalizing σ''", "induction Hup")],
    expected_intent="Shorten the induction by dropping `generalizing σ''`, believing the final store need not vary; "
                    "observed in Lean: passes without error because σ'' is invariant across UpdateStates steps.",
    gold_alternatives=[[("induction Hup", "induction Hup generalizing σ''")]],
    gold_strategy="original restored (candidate itself was unexpectedly valid; gold records original baseline)",
    prediction="failure in update_some where ih is applied to a different store -> escalate (block/body)",
)

# R06b induction context lost (additional variant that actually fails & escalates) --------
CASES["R06b"] = strata(S3, 3, SSP, "Core.InitsUpdatesComm") | dict(
    mutation=[("  have Hk : (isDefined σ' ks) := UpdateStatesDefined Hup\n", "")],
    expected_intent="Remove the pre-induction auxiliary step `have Hk : (isDefined σ' ks) := UpdateStatesDefined Hup` "
                    "before `induction Hup generalizing σ''`, losing `Hk` from the induction hypothesis context.",
    gold_alternatives=[[("  have Hlen1 := InitStatesLength Hinit\n",
                         "  have Hk : (isDefined σ' ks) := UpdateStatesDefined Hup\n  have Hlen1 := InitStatesLength Hinit\n")]],
    gold_strategy="restore the pre-induction auxiliary hypothesis `Hk` before `induction Hup`",
    prediction="in update_some, `ih` or `simp_all` fails because `isDefined` is missing from induction context -> escalate",
)

# R07 unavailable lemma name -------------------------------------------------------------
CASES["R07"] = strata(S1, 1, CE, "CallElimCorrect.substOldPostSubset") | dict(
    mutation=[("List.Subset.app", "List.append_subset_of_subset", "all")],
    expected_intent="Replace the project-local helper `List.Subset.app` by a guessed standard-library style name "
                    "(`List.append_subset_of_subset`) everywhere in the proof.",
    gold_alternatives=[
        [("apply List.append_subset_of_subset", "refine List.append_subset.mpr ⟨?_, ?_⟩", "all")],
        [("List.append_subset_of_subset", "List.Subset.app", "all")],
    ],
    gold_strategy="first try: use the real core lemma List.append_subset (intent: library lemma instead of "
                  "local helper); fallback: original helper restored",
    prediction="unknown identifier at the first apply; ops cannot fix all occurrences -> escalate",
)

# R08 local fix, downstream dependency -----------------------------------------------------
CASES["R08"] = strata(S1, 1, CE, "CallElimCorrect.substOldPostSubset") | dict(
    mutation=[("case fvar =>\n    intros x Hin\n    rename_i m name ty2\n", "case fvar =>\n    intros x Hin\n")],
    expected_intent="Delete the `rename_i m name ty2` line of the fvar case as cosmetic; the following "
                    "`simp at m/name/ty2` lines depend on those names.",
    gold_alternatives=[
        [("case fvar =>\n    intros x Hin\n    simp at m\n    simp at name\n    simp at ty2\n\n    simp_all",
          "case fvar =>\n    intros x Hin\n    simp_all")],
        [("case fvar =>\n    intros x Hin\n", "case fvar =>\n    intros x Hin\n    rename_i m name ty2\n")],
    ],
    gold_strategy="first try: also delete the name-dependent simp lines (intent: remove auxiliary steps); "
                  "fallback: original restored",
    prediction="first error at `simp at m` (or name); deleting it moves the error to the next line -> full replay fails",
)
