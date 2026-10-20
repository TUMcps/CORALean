module

public import CORALean.Specification.STL.Operations.ExprIsLinear
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A linear expression is affine

An expression that passes `isLinearPredicate`'s test is an affine function of the state:
`e(x) = Σᵢ aᵢ xᵢ + b`.

## Inputs
* `e` – expression

## Hypotheses
* `h` – the expression is linear

## Conclusion
* the expression is an affine function of the variables
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped BigOperators

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem STL.Expr.aux_isLinear_mul {e₁ e₂ : STL.Expr n} (h : (STL.Expr.mul e₁ e₂).isLinear = true) :
    (∃ c, e₁ = .num c ∧ e₂.isLinear = true) ∨ (∃ c, e₂ = .num c ∧ e₁.isLinear = true) := by
  cases e₁ <;> cases e₂ <;> simp_all [STL.Expr.isLinear]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Expr.exists_affine_of_isLinear (e : STL.Expr n) (h : e.isLinear = true) :
    ∃ (a : Fin n → ℝ) (b : ℝ), ∀ x, e.eval x = ∑ i, a i * x i + b := by -- --- PROOF ---
  induction e with
  -- the base cases
  | var i => exact ⟨fun j => if j = i then 1 else 0, 0, fun x => by simp [STL.Expr.eval]⟩
  | num c => exact ⟨0, c, fun x => by simp [STL.Expr.eval]⟩
  -- sums and differences add the coefficients
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [STL.Expr.isLinear, Bool.and_eq_true] at h
    obtain ⟨a₁, b₁, h₁⟩ := ih₁ h.1
    obtain ⟨a₂, b₂, h₂⟩ := ih₂ h.2
    refine ⟨a₁ + a₂, b₁ + b₂, fun x => ?_⟩
    simp only [STL.Expr.eval, h₁, h₂, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  | sub e₁ e₂ ih₁ ih₂ =>
    simp only [STL.Expr.isLinear, Bool.and_eq_true] at h
    obtain ⟨a₁, b₁, h₁⟩ := ih₁ h.1
    obtain ⟨a₂, b₂, h₂⟩ := ih₂ h.2
    refine ⟨a₁ - a₂, b₁ - b₂, fun x => ?_⟩
    simp only [STL.Expr.eval, h₁, h₂, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  -- a product by a number scales them
  | mul e₁ e₂ ih₁ ih₂ =>
    rcases STL.Expr.aux_isLinear_mul h with ⟨c, rfl, h'⟩ | ⟨c, rfl, h'⟩
    · obtain ⟨a, b, hab⟩ := ih₂ h'
      refine ⟨c • a, c * b, fun x => ?_⟩
      have hs : ∀ i, (c • a) i * x i = c * (a i * x i) := fun i => by simp [mul_assoc]
      simp only [STL.Expr.eval, hab, hs, ← Finset.mul_sum]
      ring
    · obtain ⟨a, b, hab⟩ := ih₁ h'
      refine ⟨c • a, c * b, fun x => ?_⟩
      have hs : ∀ i, (c • a) i * x i = c * (a i * x i) := fun i => by simp [mul_assoc]
      simp only [STL.Expr.eval, hab, hs, ← Finset.mul_sum]
      ring
  -- a power is not linear
  | pow e k ih => simp [STL.Expr.isLinear] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
