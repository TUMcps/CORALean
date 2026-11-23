module

public import CORALean.ContSet.ConZonotope.Real.Operations.DualBound
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# The dual bound is a lower bound (weak duality)

`wᵀ β = (w + Cᵀ λ)ᵀ β - λᵀ (C β)`. The first term is at least `-‖w + Cᵀ λ‖₁` on the box, and the
second at most `λᵀ d` where `C β ≤ d` and `λ ≥ 0`.

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `w` – coefficients of the bounded form
* `lam` – multipliers
* `β` – factors

## Hypotheses
* `hlam` – the multipliers are not negative
* `hβ` – the factors lie in the unit box
* `hC` – the factors satisfy the constraints

## Conclusion
* the dual bound is at most `wᵀ β`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.dualBound_le (C : Mat ℝ p q) (d : Vec ℝ p) (w : Vec ℝ q) (lam : Vec ℝ p)
    (β : Vec ℝ q) (hlam : ∀ i, 0 ≤ lam i) (hβ : ∀ j, |β j| ≤ 1)
    (hC : ∀ i, ∑ j, C i j * β j ≤ d i) : -- --- CONCL ---
    ConZonotope.dualBound C d w lam ≤ ∑ j, w j * β j := by -- --- PROOF ---
  -- each coefficient of the Lagrangian costs at most its absolute value on the box
  have hbox : -(∑ j, |w j + ∑ i, lam i * C i j|)
      ≤ ∑ j, (w j + ∑ i, lam i * C i j) * β j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have h := abs_mul (w j + ∑ i, lam i * C i j) (β j)
    have hle : |w j + ∑ i, lam i * C i j| * |β j| ≤ |w j + ∑ i, lam i * C i j| :=
      mul_le_of_le_one_right (abs_nonneg _) (hβ j)
    linarith [neg_abs_le ((w j + ∑ i, lam i * C i j) * β j)]
  -- the multipliers' term, `λᵀ (C β) ≤ λᵀ d`
  have hrows : ∑ i, lam i * ∑ j, C i j * β j ≤ ∑ i, lam i * d i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hC i) (hlam i)
  -- `Cᵀ λ` against `β` is `λ` against `C β`
  have hswap : ∑ j, (∑ i, lam i * C i j) * β j = ∑ i, lam i * ∑ j, C i j * β j := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hsplit : ∑ j, (w j + ∑ i, lam i * C i j) * β j
      = ∑ j, w j * β j + ∑ j, (∑ i, lam i * C i j) * β j := by
    rw [← Finset.sum_add_distrib]; simp_rw [add_mul]
  show -(∑ j, |w j + ∑ i, lam i * C i j|) - ∑ i, lam i * d i ≤ _
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
