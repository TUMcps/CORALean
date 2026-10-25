module

public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeConjunctiveNormalForm
public import CORALean.Specification.STL.Operations.TreeDisjunctiveNormalForm
public import CORALean.Specification.STL.Theorems.TreeMemAssignIdentifiersFrom
public import CORALean.Specification.STL.Theorems.TreeSatCompare
public import CORALean.Specification.STL.Theorems.TreeSatNnfWith

@[expose] public section

/-!
# `STL/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- ===================================  `STL.Cmp.rel_negate`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `negate` is the comparison that fails where the original holds. -/
theorem STL.Cmp.rel_negate (op : STL.Cmp) (a b : ℝ) : op.negate.Relates a b ↔ ¬ op.Relates a b := by
  cases op <;> simp [STL.Cmp.negate, STL.Cmp.Relates]


-- ==================================  `STL.Expr.eval_minus`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus.m` builds the difference. -/
theorem STL.Expr.eval_minus (e₁ e₂ : STL.Expr n) (x : Fin n → ℝ) :
    (STL.Expr.minus e₁ e₂).eval x = e₁.eval x - e₂.eval x := rfl


-- ===================================  `STL.Expr.eval_plus`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus.m` builds the sum, whichever operand is the number. -/
theorem STL.Expr.eval_plus (e₁ e₂ : STL.Expr n) (x : Fin n → ℝ) :
    (STL.Expr.plus e₁ e₂).eval x = e₁.eval x + e₂.eval x := by
  cases e₁ <;> simp [STL.Expr.plus, STL.Expr.eval, add_comm]


-- ==================================  `STL.Expr.eval_power`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `power.m` builds the power. -/
theorem STL.Expr.eval_power (e : STL.Expr n) (k : ℤ) (x : Fin n → ℝ) :
    (STL.Expr.power e k).eval x = e.eval x ^ k := rfl


-- ==================================  `STL.Expr.eval_times`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times.m` builds the product, whichever operand is the number. -/
theorem STL.Expr.eval_times (e₁ e₂ : STL.Expr n) (x : Fin n → ℝ) :
    (STL.Expr.times e₁ e₂).eval x = e₁.eval x * e₂.eval x := by
  cases e₁ <;> cases e₂ <;> simp [STL.Expr.times, STL.Expr.eval, mul_comm]


-- ====================================  `STL.Tree.sat_ge`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ge.m` builds the comparison `e₁ >= e₂`. -/
theorem STL.Tree.sat_ge (e₁ e₂ : STL.Expr n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.ge e₁ e₂).Satisfies ξ ↔ e₁.eval (ξ 0) ≥ e₂.eval (ξ 0) := STL.Tree.sat_compare .ge e₁
        e₂ ξ


-- ====================================  `STL.Tree.sat_gt`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `gt.m` builds the comparison `e₁ > e₂`. -/
theorem STL.Tree.sat_gt (e₁ e₂ : STL.Expr n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.gt e₁ e₂).Satisfies ξ ↔ e₁.eval (ξ 0) > e₂.eval (ξ 0) := STL.Tree.sat_compare .gt e₁
        e₂ ξ


-- ==================================  `STL.Tree.sat_implies`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `implies.m` builds the classical implication. -/
theorem STL.Tree.sat_implies (φ ψ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.implies φ ψ).Satisfies ξ ↔ (φ.Satisfies ξ → ψ.Satisfies ξ) := imp_iff_not_or.symm


-- ====================================  `STL.Tree.sat_le`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `le.m` builds the comparison `e₁ <= e₂`. -/
theorem STL.Tree.sat_le (e₁ e₂ : STL.Expr n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.le e₁ e₂).Satisfies ξ ↔ e₁.eval (ξ 0) ≤ e₂.eval (ξ 0) := STL.Tree.sat_compare .le e₁
        e₂ ξ


-- ====================================  `STL.Tree.sat_lt`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `lt.m` builds the comparison `e₁ < e₂`. -/
theorem STL.Tree.sat_lt (e₁ e₂ : STL.Expr n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (STL.Tree.lt e₁ e₂).Satisfies ξ ↔ e₁.eval (ξ 0) < e₂.eval (ξ 0) := STL.Tree.sat_compare .lt e₁
        e₂ ξ


-- ============================  `STL.Tree.sat_negationNormalForm`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `negationNormalForm` keeps the meaning of a formula. -/
theorem STL.Tree.sat_negationNormalForm (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) :
    φ.negationNormalForm.Satisfies ξ ↔ φ.Satisfies ξ :=
  (STL.Tree.sat_nnfWith STL.Cmp.negate STL.Cmp.rel_negate φ false ξ).trans (by simp)


-- =======================  `STL.Tree.temporal_of_mem_assignIdentifiers`  ======================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every listed formula of `assignIdentifiers` is non-temporal. -/
theorem STL.Tree.temporal_of_mem_assignIdentifiers (φ ψ : STL.Tree n)
    (h : ψ ∈ φ.assignIdentifiers) : ψ.temporal = false :=
  (STL.Tree.temporal_of_mem_assignIdentifiersFrom φ [] ψ h).resolve_left (by simp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
