module

public import CORALean.ContSet.ConZonotope.Real.Operations.IntervalOfFactorBounds
public import CORALean.ContSet.ConZonotope.Real.Operations.Constrain
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The image of the factor bounds encloses the constrained zonotope

[1, Eq. 13], corrected: if `[β̲, β̄]` contains every factor `β ∈ B_q` with `C β ≤ d`, then
`Z|_{C≤d} ⊆ c ⊕ [G⁺ β̲ + G⁻ β̄, G⁺ β̄ + G⁻ β̲]` (`Zonotope.intervalOfFactorBounds`): entry by entry,
`G(i,j) β(j) = G⁺(i,j) β(j) + G⁻(i,j) β(j)` with `G⁺ ≥ 0` and `G⁻ ≤ 0`. The printed signs fail
(`Zonotope.intervalOfFactorBoundsPrinted_counterexample`).

## Inputs
* `Z` – zonotope
* `C` – constraint matrix on the factors
* `d` – constraint offset
* `B` – bounds of the factors

## Hypotheses
* `hB` – `B` contains every factor in the unit box that meets the constraints

## Conclusion
* `Z|_{C≤d}` lies in the interval

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations,
      2026.](../../../../../../references/2026/koller-iclr-latent-space.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 13], corrected: factor bounds of the constrained hypercube bound `Z|_{C≤d}`. -/
theorem Zonotope.intervalOfFactorBounds_outer (Z : Zonotope (Vec ℝ n)) (C : Mat ℝ p Z.h)
    (d : Vec ℝ p) (B : Interval (Vec ℝ Z.h))
    (hB : ∀ β : Vec ℝ Z.h, (∀ j, |β j| ≤ 1) → β ∈ (HPolytope.ineqs C d).construct →
      β ∈ B.construct) : -- --- CONCL ---
    (Z.constrain C d).construct ⊆ (Z.intervalOfFactorBounds B).construct := by -- --- PROOF ---
  intro x hx i
  obtain ⟨β, hβ, hP, rfl⟩ : ∃ β : Fin Z.h → ℝ, (∀ j, |β j| ≤ 1) ∧
      β ∈ (HPolytope.ineqs C d).construct ∧ x = Z.c + ∑ j, β j • Z.G j := hx
  have hβB : ∀ j, B.inf j ≤ β j ∧ β j ≤ B.sup j := hB β hβ hP
  change Z.c i + ∑ j, (Z.G j i + |Z.G j i|) / 2 * B.inf j +
      ∑ j, (Z.G j i - |Z.G j i|) / 2 * B.sup j ≤ (Z.c + ∑ j, β j • Z.G j) i ∧
    (Z.c + ∑ j, β j • Z.G j) i ≤ Z.c i + ∑ j, (Z.G j i + |Z.G j i|) / 2 * B.sup j +
      ∑ j, (Z.G j i - |Z.G j i|) / 2 * B.inf j
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- entry by entry, `G⁺ ≥ 0` meets one end of `[β̲(j), β̄(j)]` and `G⁻ ≤ 0` the other
  have hterm : ∀ j, (Z.G j i + |Z.G j i|) / 2 * B.inf j + (Z.G j i - |Z.G j i|) / 2 * B.sup j ≤
      β j * Z.G j i ∧ β j * Z.G j i ≤
      (Z.G j i + |Z.G j i|) / 2 * B.sup j + (Z.G j i - |Z.G j i|) / 2 * B.inf j := by
    intro j
    have hp : 0 ≤ (Z.G j i + |Z.G j i|) / 2 := by linarith [neg_abs_le (Z.G j i)]
    have hm : (Z.G j i - |Z.G j i|) / 2 ≤ 0 := by linarith [le_abs_self (Z.G j i)]
    have h1 := mul_le_mul_of_nonneg_left (hβB j).1 hp
    have h2 := mul_le_mul_of_nonpos_left (hβB j).2 hm
    have h3 := mul_le_mul_of_nonneg_left (hβB j).2 hp
    have h4 := mul_le_mul_of_nonpos_left (hβB j).1 hm
    constructor <;> nlinarith
  have hlo := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (hterm j).1
  have hhi := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (hterm j).2
  simp only [Finset.sum_add_distrib] at hlo hhi
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
