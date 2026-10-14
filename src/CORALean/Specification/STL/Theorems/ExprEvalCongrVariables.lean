module

public import CORALean.Specification.STL.Operations.ExprVariables

@[expose] public section

/-!
# An expression reads only its variables

Two states that agree on the variables of an expression give it the same value.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Expr.eval_congr_variables (e : STL.Expr n) {x y : Fin n → ℝ}
    (h : ∀ i ∈ e.variables, x i = y i) : e.eval x = e.eval y := by -- --- PROOF ---
  induction e with
  | var i => exact h i (by simp [STL.Expr.variables])
  | num c => rfl
  | add e₁ e₂ ih₁ ih₂ | sub e₁ e₂ ih₁ ih₂ | mul e₁ e₂ ih₁ ih₂ =>
    simp only [STL.Expr.eval, ih₁ fun i hi => h i (by simp [STL.Expr.variables, hi]),
      ih₂ fun i hi => h i (by simp [STL.Expr.variables, hi])]
  | pow e k ih => simp only [STL.Expr.eval, ih h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
