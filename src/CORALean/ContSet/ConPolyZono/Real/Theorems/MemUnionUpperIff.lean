module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpper
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemAndRowsIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConValue
public import CORALean.ContSet.ConPolyZono.Real.Operations.ProdAddCol
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEqUnit
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# What the two selector rows say

`α₁α₂ = 1` and the selector polynomial `= 0`: the two equations Appendix A of
[1, Thm. 1] solves to cut the factor cube down to the union of the two branch
domains. The two rows are two systems stacked over the same factors, so each is read on its own
(`PolyLevelSet.mem_andRows_iff`).

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The selector rows hold exactly when the factors are in the unit box, `α₁α₂ = 1` and the
selector polynomial vanishes. -/
theorem ConPolyZono.mem_unionUpper_iff {p₁ p₂ : ℕ} (a : Fin (p₁ + p₂ + 2) → ℝ) : -- --- STMT ---
    a ∈ (ConPolyZono.unionUpper p₁ p₂).construct
      ↔ (∀ k, |a k| ≤ 1) ∧ (a (ConPolyZono.unionSel p₁ p₂) * a (Fin.natAdd (p₁ + p₂) 1) = 1
        ∧ (1 + a (ConPolyZono.unionSel p₁ p₂)
              + 2⁻¹ * ConPolyZono.unionMeanSq (fun j => a (Fin.castAdd 2 (Fin.castAdd p₂ j)))
                * (1 - a (ConPolyZono.unionSel p₁ p₂)))
            * (1 - 2⁻¹
              * ConPolyZono.unionMeanSq (fun k => a (Fin.castAdd 2 (Fin.natAdd p₁ k))))
          - a (Fin.natAdd (p₁ + p₂) 1) - 1 = 0) := by -- --- PROOF ---
  -- the two rows, each a system of its own over the same factors
  have hsplit : a ∈ (ConPolyZono.unionUpper p₁ p₂).construct
      ↔ ((∀ k, |a k| ≤ 1) ∧ ∀ i : Fin 1, ((fun _ _ => (1 : ℝ)) *ᵥ
          PolyZonotope.monomial (fun k (_ : Fin 1) =>
            ConPolyZono.unitCol (ConPolyZono.unionSel p₁ p₂) 1 k
              + ConPolyZono.unitCol (Fin.natAdd (p₁ + p₂) 1) 1 k) a) i = 1)
        ∧ ∀ i : Fin 1, ((fun _ l => ConPolyZono.unionConCoef p₁ p₂ l) *ᵥ
            PolyZonotope.monomial (fun k l => ConPolyZono.unionConCol p₁ p₂ l k) a) i
          - (0 : Vec ℝ 1) i = 0 := by
    rw [ConPolyZono.unionUpper, PolyLevelSet.mem_andRows_iff,
      PolyLevelSet.mem_construct_iff_of_eq_unit (fun _ => rfl) rfl]
    rfl
  rw [hsplit]
  constructor
  · rintro ⟨⟨hb, h₁⟩, h₂⟩
    refine ⟨hb, ?_, ?_⟩
    · -- the `α₁α₂` row, its single column evaluated
      have h := h₁ 0
      simp only [Matrix.mulVec, dotProduct, Finset.univ_unique,
        Fin.default_eq_zero, one_mul, Finset.sum_singleton, PolyZonotope.monomial] at h
      rw [ConPolyZono.prod_addCol, ConPolyZono.prod_unitCol, ConPolyZono.prod_unitCol,
        pow_one, pow_one] at h
      exact h
    · have h := h₂ 0
      simp only [Matrix.mulVec, dotProduct, PolyZonotope.monomial, Pi.zero_apply, sub_zero] at h
      rw [ConPolyZono.unionCon_value] at h
      exact h
  · rintro ⟨hb, h₁, h₂⟩
    refine ⟨⟨hb, ?_⟩, ?_⟩
    · intro i
      fin_cases i
      simp only [Matrix.mulVec, dotProduct, Finset.univ_unique,
        Fin.default_eq_zero, one_mul, Finset.sum_singleton, PolyZonotope.monomial]
      rw [ConPolyZono.prod_addCol, ConPolyZono.prod_unitCol, ConPolyZono.prod_unitCol,
        pow_one, pow_one, h₁]
    · -- the selector row, at the value `unionCon_value` computes
      intro i
      fin_cases i
      simp only [Matrix.mulVec, dotProduct, PolyZonotope.monomial, Pi.zero_apply, sub_zero]
      rw [ConPolyZono.unionCon_value, h₂]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
