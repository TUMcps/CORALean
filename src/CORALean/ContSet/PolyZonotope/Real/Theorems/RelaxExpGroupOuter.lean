module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGroup
public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLeSum
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Merging any group of dependent generators over-approximates

`relaxExpMulti_outer` once per group member. Each member drifts from the target
monomial by at most the summed `ξ_E` between their columns, `[1, Prop. 4]`, and
that drift is what its own independent generator carries; the target's monomial
factors out of the group and the rest cancels.

Nothing relates the members to each other or to the target, so no hypothesis
constrains the grouping — as `reduceBy_outer` holds at every partition, and
`k = 0` leaves a renamed set and an inclusion that is the identity.

Each member asks one scalar of its generator, `Zonotope.coefficient`, degenerate
width included, which is why this holds over any module.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Merging any group of dependent generators onto any kept one
over-approximates, whichever partition names the group. -/
theorem PolyZonotope.relaxExpGroup_outer (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin k)) (t : Fin d) :
    pZ.construct ⊆ (pZ.relaxExpGroup part t).construct := by -- --- PROOF ---
  rintro x ⟨a, β, ha, hβ, rfl⟩
  -- every member drifts from the target by at most the width it pays
  have habs : ∀ l : Fin k, |PolyZonotope.monomial pZ.E a (part.right l)
      - PolyZonotope.monomial pZ.E a (part.left t)|
        ≤ (pZ.relaxWidthGroup part t l : ℝ) := fun l => by
    rw [PolyZonotope.relaxWidthGroup, Nat.cast_sum]
    exact PolyZonotope.abs_sub_monomial_le_sum pZ.E ha _ _
  set cf : Fin k → ℝ := fun l => Zonotope.coefficient (pZ.relaxWidthGroup part t l : ℝ)
    (PolyZonotope.monomial pZ.E a (part.right l)
      - PolyZonotope.monomial pZ.E a (part.left t)) with hcf
  have hcoef : ∀ l, cf l * (pZ.relaxWidthGroup part t l : ℝ)
      = PolyZonotope.monomial pZ.E a (part.right l)
        - PolyZonotope.monomial pZ.E a (part.left t) := fun l => by
    rw [hcf, mul_comm]
    exact Zonotope.mul_coefficient (habs l)
  -- the kept columns keep their monomials, the group taking the target's
  have hmono : ∀ l : Fin d, PolyZonotope.monomial (pZ.relaxExpGroup part t).E a l
      = PolyZonotope.monomial pZ.E a (part.left l) := fun _ => rfl
  -- the target's monomial factors out of the group, the drift staying behind
  have hgroup : ∑ l : Fin k, PolyZonotope.monomial pZ.E a (part.right l) • pZ.G (part.right l)
      = PolyZonotope.monomial pZ.E a (part.left t) • ∑ l : Fin k, pZ.G (part.right l)
        + ∑ l : Fin k, (cf l * (pZ.relaxWidthGroup part t l : ℝ)) • pZ.G (part.right l) := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hcoef l, ← add_smul]
    congr 1
    ring
  -- the same factors read both sides, with one coefficient appended per member
  refine ⟨a, Fin.append β cf, ha, ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) fun l => ?_
    · rw [Fin.append_left]
      exact hβ j
    · rw [Fin.append_right]
      exact Zonotope.abs_coefficient_le_one (Nat.cast_nonneg _) (habs l)
  show pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i + ∑ j, β j • pZ.GI j
      = pZ.c + (∑ l : Fin d, PolyZonotope.monomial (pZ.relaxExpGroup part t).E a l
          • (pZ.relaxExpGroup part t).G l)
        + ∑ j : Fin (pZ.q + k), Fin.append β cf j • (pZ.relaxExpGroup part t).GI j
  rw [part.sum_split₂ fun i => PolyZonotope.monomial pZ.E a i • pZ.G i, Fin.sum_univ_add, hgroup]
  simp only [hmono]
  simp only [PolyZonotope.relaxExpGroup, Fin.append_left, Fin.append_right,
    smul_add, smul_ite, smul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, smul_smul]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
