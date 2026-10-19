module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpper
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.AndExact
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConValue
public import CORALean.ContSet.ConPolyZono.Real.Operations.ProdAddCol
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# What the two selector rows say

`α₁α₂ = 1` and the selector polynomial `= 0`: the two equations Appendix A of
[1, Thm. 1] solves to cut the factor cube down to the union of the two branch
domains. The two rows are two systems stacked over the same factors, so each is read on its own
(`PolyLevelSet.and_exact`).

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The selector rows hold exactly when `α₁α₂ = 1` and the selector polynomial vanishes. -/
theorem ConPolyZono.mem_unionUpper_iff {p₁ p₂ : ℕ} (a : Fin (p₁ + p₂ + 2) → ℝ) : -- --- STMT ---
    a ∈ (ConPolyZono.unionUpper p₁ p₂).construct
      ↔ (a (ConPolyZono.unionSel p₁ p₂) * a (Fin.natAdd (p₁ + p₂) 1) = 1
        ∧ (1 + a (ConPolyZono.unionSel p₁ p₂)
              + 2⁻¹ * ConPolyZono.unionMeanSq (fun j => a (Fin.castAdd 2 (Fin.castAdd p₂ j)))
                * (1 - a (ConPolyZono.unionSel p₁ p₂)))
            * (1 - 2⁻¹
              * ConPolyZono.unionMeanSq (fun k => a (Fin.castAdd 2 (Fin.natAdd p₁ k))))
          - a (Fin.natAdd (p₁ + p₂) 1) - 1 = 0) := by -- --- PROOF ---
  -- the two rows, each a system of its own over the same factors
  have hsplit : a ∈ (ConPolyZono.unionUpper p₁ p₂).construct
      ↔ (∀ i : Fin 1, ((fun _ _ => (1 : ℝ)) *ᵥ PolyZonotope.monomial (fun k (_ : Fin 1) =>
            ConPolyZono.unitCol (ConPolyZono.unionSel p₁ p₂) 1 k
              + ConPolyZono.unitCol (Fin.natAdd (p₁ + p₂) 1) 1 k) a) i = 1)
        ∧ ∀ i : Fin 1, ((fun _ l => ConPolyZono.unionConCoef p₁ p₂ l) *ᵥ
            PolyZonotope.monomial (fun k l => ConPolyZono.unionConCol p₁ p₂ l k) a) i
          = (0 : Vec ℝ 1) i := by
    rw [ConPolyZono.unionUpper, PolyLevelSet.and_exact, Set.mem_inter_iff,
      PolyLevelSet.mem_construct_iff_of_eq fun _ => rfl,
      PolyLevelSet.mem_construct_iff_of_eq fun _ => rfl]
    rfl
  rw [hsplit]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · -- the `α₁α₂` row, its single column evaluated
      have h := h₁ 0
      simp only [Matrix.mulVec, dotProduct, Finset.univ_unique,
        Fin.default_eq_zero, one_mul, Finset.sum_singleton, PolyZonotope.monomial] at h
      rw [ConPolyZono.prod_addCol, ConPolyZono.prod_unitCol, ConPolyZono.prod_unitCol,
        pow_one, pow_one] at h
      exact h
    · have h := h₂ 0
      simp only [Matrix.mulVec, dotProduct, PolyZonotope.monomial] at h
      rw [ConPolyZono.unionCon_value] at h
      simpa only [Pi.zero_apply] using h
  · rintro ⟨h₁, h₂⟩
    constructor
    · intro i
      fin_cases i
      simp only [Matrix.mulVec, dotProduct, Finset.univ_unique,
        Fin.default_eq_zero, one_mul, Finset.sum_singleton, PolyZonotope.monomial]
      rw [ConPolyZono.prod_addCol, ConPolyZono.prod_unitCol, ConPolyZono.prod_unitCol,
        pow_one, pow_one, h₁]
    · -- the selector row, at the value `unionCon_value` computes
      intro i
      fin_cases i
      simp only [Matrix.mulVec, dotProduct, PolyZonotope.monomial]
      rw [ConPolyZono.unionCon_value, h₂]
      rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
