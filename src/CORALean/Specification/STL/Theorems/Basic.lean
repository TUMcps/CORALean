module

public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Theorems.TreeSatCompare
public import CORALean.Specification.STL.Theorems.TreeSatEliminateTrueFalseWith
public import CORALean.Specification.STL.Theorems.TreeSatNnfWith

@[expose] public section

/-!
# `STL/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ===================================  `STL.Cmp.rel_negate`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

/-- `negate` is the comparison that fails where the original holds. -/
theorem STL.Cmp.rel_negate (op : STL.Cmp) (a b : ℝ) : op.negate.rel a b ↔ ¬ op.rel a b := by
  cases op <;> simp [STL.Cmp.negate, STL.Cmp.rel]

end CORALean


-- ==================================  `STL.Expr.eval_minus`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `minus.m` builds the difference. -/
theorem STL.Expr.eval_minus (e₁ e₂ : STL.Expr n) (x : Fin n → ℝ) :
    (STL.Expr.minus e₁ e₂).eval x = e₁.eval x - e₂.eval x := rfl

end CORALean


-- ===================================  `STL.Expr.eval_plus`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `plus.m` builds the sum, whichever operand is the number. -/
theorem STL.Expr.eval_plus (e₁ e₂ : STL.Expr n) (x : Fin n → ℝ) :
    (STL.Expr.plus e₁ e₂).eval x = e₁.eval x + e₂.eval x := by
  cases e₁ <;> simp [STL.Expr.plus, STL.Expr.eval, add_comm]

end CORALean


-- ==================================  `STL.Expr.eval_power`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `power.m` builds the power. -/
theorem STL.Expr.eval_power (e : STL.Expr n) (k : ℤ) (x : Fin n → ℝ) :
    (STL.Expr.power e k).eval x = e.eval x ^ k := rfl

end CORALean


-- ==================================  `STL.Expr.eval_times`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n : ℕ}

/-- `times.m` builds the product, whichever operand is the number. -/
theorem STL.Expr.eval_times (e₁ e₂ : STL.Expr n) (x : Fin n → ℝ) :
    (STL.Expr.times e₁ e₂).eval x = e₁.eval x * e₂.eval x := by
  cases e₁ <;> cases e₂ <;> simp [STL.Expr.times, STL.Expr.eval, mul_comm]

end CORALean


-- ============================  `STL.Tree.sat_eliminateTrueFalse`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open scoped NNReal

variable {n : ℕ}

/-- `eliminateTrueFalse` keeps the meaning of a formula with non-empty intervals. -/
theorem STL.Tree.sat_eliminateTrueFalse (φ : STL.Tree n) (hφ : φ.WellFormed)
    (ξ : ℝ≥0 → Fin n → ℝ) : φ.eliminateTrueFalse.Sat ξ ↔ φ.Sat ξ :=
  STL.Tree.sat_eliminateTrueFalseWith _ (fun _ _ _ _ => Iff.rfl) φ hφ ξ

end CORALean


-- ====================================  `STL.Tree.sat_ge`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open scoped NNReal

variable {n : ℕ}

/-- `ge.m` builds the comparison `e₁ >= e₂`. -/
theorem STL.Tree.sat_ge (e₁ e₂ : STL.Expr n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.ge e₁ e₂).Sat ξ ↔ e₁.eval (ξ 0) ≥ e₂.eval (ξ 0) := STL.Tree.sat_compare .ge e₁ e₂ ξ

end CORALean


-- ====================================  `STL.Tree.sat_gt`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open scoped NNReal

variable {n : ℕ}

/-- `gt.m` builds the comparison `e₁ > e₂`. -/
theorem STL.Tree.sat_gt (e₁ e₂ : STL.Expr n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.gt e₁ e₂).Sat ξ ↔ e₁.eval (ξ 0) > e₂.eval (ξ 0) := STL.Tree.sat_compare .gt e₁ e₂ ξ

end CORALean


-- ==================================  `STL.Tree.sat_implies`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open scoped NNReal

variable {n : ℕ}

/-- `implies.m` builds the classical implication. -/
theorem STL.Tree.sat_implies (φ ψ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.implies φ ψ).Sat ξ ↔ (φ.Sat ξ → ψ.Sat ξ) := imp_iff_not_or.symm

end CORALean


-- ====================================  `STL.Tree.sat_le`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open scoped NNReal

variable {n : ℕ}

/-- `le.m` builds the comparison `e₁ <= e₂`. -/
theorem STL.Tree.sat_le (e₁ e₂ : STL.Expr n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.le e₁ e₂).Sat ξ ↔ e₁.eval (ξ 0) ≤ e₂.eval (ξ 0) := STL.Tree.sat_compare .le e₁ e₂ ξ

end CORALean


-- ====================================  `STL.Tree.sat_lt`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open scoped NNReal

variable {n : ℕ}

/-- `lt.m` builds the comparison `e₁ < e₂`. -/
theorem STL.Tree.sat_lt (e₁ e₂ : STL.Expr n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.lt e₁ e₂).Sat ξ ↔ e₁.eval (ξ 0) < e₂.eval (ξ 0) := STL.Tree.sat_compare .lt e₁ e₂ ξ

end CORALean


-- ============================  `STL.Tree.sat_negationNormalForm`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

open scoped NNReal

variable {n : ℕ}

/-- `negationNormalForm` keeps the meaning of a formula. -/
theorem STL.Tree.sat_negationNormalForm (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) :
    φ.negationNormalForm.Sat ξ ↔ φ.Sat ξ :=
  (STL.Tree.sat_nnfWith STL.Cmp.negate STL.Cmp.rel_negate φ false ξ).trans (by simp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
