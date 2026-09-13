import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpperA
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpperB
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpperEC
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsSharedIff
import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConValue
import CORALean.ContSet.ConPolyZono.Real.Operations.ProdAddCol

/-!
# What the two selector rows say

`α₁α₂ = 1` and the selector polynomial `= 0`: the two equations Appendix A of
[1, Thm. 1] solves to cut the factor cube down to the union of the two branch
domains. Both right-hand sides are points, so a row's pair of bounds is one
equation.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.holds_unionUpper_iff {p₁ p₂ : ℕ} (a : Fin (p₁ + p₂ + 2) → ℝ) :
    ConPolyZono.holds (ConPolyZono.unionUpperA p₁ p₂) ConPolyZono.unionUpperB
        (ConPolyZono.unionUpperEC p₁ p₂) a
      ↔ (a (ConPolyZono.unionSel p₁ p₂) * a (Fin.natAdd (p₁ + p₂) 1) = 1
        ∧ (1 + a (ConPolyZono.unionSel p₁ p₂)
              + 2⁻¹ * ConPolyZono.unionMeanSq (fun j => a (Fin.castAdd 2 (Fin.castAdd p₂ j)))
                * (1 - a (ConPolyZono.unionSel p₁ p₂)))
            * (1 - 2⁻¹
              * ConPolyZono.unionMeanSq (fun k => a (Fin.castAdd 2 (Fin.natAdd p₁ k))))
          - a (Fin.natAdd (p₁ + p₂) 1) - 1 = 0) := by -- --- PROOF ---
  rw [ConPolyZono.unionUpperA, ConPolyZono.unionUpperB, ConPolyZono.unionUpperEC,
    ConPolyZono.holds_shared_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · -- the `α₁α₂` row, its single column evaluated
      have h := h₁ 0
      simp only [Interval.point, Matrix.mulVec, dotProduct, Finset.univ_unique,
        Fin.default_eq_zero, one_mul, Finset.sum_singleton, PolyZonotope.monomial] at h
      rw [ConPolyZono.prod_addCol, ConPolyZono.prod_unitCol, ConPolyZono.prod_unitCol,
        pow_one, pow_one] at h
      linarith [h.1, h.2]
    · have h := h₂ 0
      simp only [Interval.point, Matrix.mulVec, dotProduct, PolyZonotope.monomial] at h
      rw [ConPolyZono.unionCon_value] at h
      simp only [Pi.zero_apply] at h
      linarith [h.1, h.2]
  · rintro ⟨h₁, h₂⟩
    constructor
    · intro i
      fin_cases i
      simp only [Interval.point, Matrix.mulVec, dotProduct, Finset.univ_unique,
        Fin.default_eq_zero, one_mul, Finset.sum_singleton, PolyZonotope.monomial]
      rw [ConPolyZono.prod_addCol, ConPolyZono.prod_unitCol, ConPolyZono.prod_unitCol,
        pow_one, pow_one, h₁]
      exact ⟨le_refl 1, le_refl 1⟩
    · -- the selector row, at the value `unionCon_value` computes
      intro i
      fin_cases i
      simp only [Interval.point, Matrix.mulVec, dotProduct, PolyZonotope.monomial]
      rw [ConPolyZono.unionCon_value, h₂]
      exact ⟨le_refl 0, le_refl 0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
