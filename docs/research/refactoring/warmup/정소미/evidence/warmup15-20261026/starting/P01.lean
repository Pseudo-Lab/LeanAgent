open OldExpressions in
theorem substOldPostSubset:
  (Imperative.HasVarsPure.getVars (P:=Expression)
    (substOld h2 (Lambda.LExpr.fvar m h1 ty) post)).Subset
    (Imperative.HasVarsPure.getVars (P:=Expression) post ++ [h1]) := by
  intro x
  simp only [Imperative.HasVarsPure.getVars, List.mem_append, List.mem_singleton]
  fun_induction substOld h2 (Lambda.LExpr.fvar m h1 ty) post <;>
    simp only [Lambda.LExpr.LExpr.getVars, List.mem_append,
      List.mem_singleton, List.not_mem_nil] <;>
    grind only []
