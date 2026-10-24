/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Typing

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file proves type safety.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

public section

namespace Cslib

variable {Var : Type*} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

open Context List Env.Wf Term Ty

variable {t : Term Var}

set_option linter.tacticAnalysis.verifyGrindOnly false in
lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t' := by
  sorry


#check Typing.progress
#print axioms Typing.progress

end LambdaCalculus.LocallyNameless.Fsub

end Cslib

#check _root_.Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress
#print axioms _root_.Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress
