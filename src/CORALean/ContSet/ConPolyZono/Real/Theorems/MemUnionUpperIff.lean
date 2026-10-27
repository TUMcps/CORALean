module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionUpper
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemAndRowsIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCoef
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionMeanSq
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionWithSel
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ProdUnitCol
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEqUnit
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# What the two selector rows say

`α₁α₂ = 1` and the selector polynomial `= 0`: the two equations Appendix A of
[1, Thm. 1] solves to cut the factor cube down to the union of the two branch
domains. The two rows are two systems stacked over the same factors, so each is read on its own
(`PolyLevelSet.mem_andRows_iff`).

## Inputs
* `p₁` – factor count of first operand
* `p₂` – factor count of second operand
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the selector rows hold exactly when factors are bounded and the polynomial vanishes

## References

* [1] [N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.](../../../../../../references/2023/kochdumper-constrained-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Columns add where monomials multiply. -/
private theorem ConPolyZono.aux_prod_addCol {p : ℕ} (a : Fin p → ℝ) (c d : Fin p → ℕ) :
    (∏ k, a k ^ (c k + d k)) = (∏ k, a k ^ c k) * ∏ k, a k ^ d k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => pow_add (a k) (c k) (d k)


/-- The monomial of a column carrying the selector. -/
private theorem ConPolyZono.aux_prod_unionWithSel {p₁ p₂ : ℕ} (a : Fin (p₁ + p₂ + 2) → ℝ)
    (c : Fin (p₁ + p₂ + 2) → ℕ) :
    (∏ k, a k ^ ConPolyZono.unionWithSel p₁ p₂ c k)
      = a (ConPolyZono.unionSel p₁ p₂) * ∏ k, a k ^ c k := by
  simp only [ConPolyZono.unionWithSel]
  rw [ConPolyZono.aux_prod_addCol, ConPolyZono.prod_unitCol, pow_one]


/-- What the selector constraint's row evaluates to. -/
private theorem ConPolyZono.aux_unionCon_value {p₁ p₂ : ℕ}
    (a : Fin (p₁ + p₂ + 2) → ℝ) : -- --- CONCL ---
    (∑ l, ConPolyZono.unionConCoef p₁ p₂ l * ∏ k, a k ^ ConPolyZono.unionConCol p₁ p₂ l k)
      = (1 + a (ConPolyZono.unionSel p₁ p₂)
            + 2⁻¹ * ConPolyZono.unionMeanSq (fun j => a (Fin.castAdd 2 (Fin.castAdd p₂ j)))
              * (1 - a (ConPolyZono.unionSel p₁ p₂)))
          * (1 - 2⁻¹ * ConPolyZono.unionMeanSq (fun k => a (Fin.castAdd 2 (Fin.natAdd p₁ k))))
        - a (Fin.natAdd (p₁ + p₂) 1) - 1 := by -- --- PROOF ---
  -- the cross group, at an arbitrary coefficient, as a product of two square sums
  have hcross : ∀ γ : ℝ,
      (∑ l : Fin (p₁ * p₂), γ * ∏ k, a k ^ ConPolyZono.unionCrossCol p₁ p₂ l k)
        = γ * ((∑ j, a (Fin.castAdd 2 (Fin.castAdd p₂ j)) ^ 2)
          * ∑ k, a (Fin.castAdd 2 (Fin.natAdd p₁ k)) ^ 2) := by
    intro γ
    have hterm : ∀ l : Fin (p₁ * p₂), (∏ k, a k ^ ConPolyZono.unionCrossCol p₁ p₂ l k)
        = a (Fin.castAdd 2 (Fin.castAdd p₂ (finProdFinEquiv.symm l).1)) ^ 2
          * a (Fin.castAdd 2 (Fin.natAdd p₁ (finProdFinEquiv.symm l).2)) ^ 2 := by
      intro l
      simp only [ConPolyZono.unionCrossCol]
      rw [ConPolyZono.aux_prod_addCol, ConPolyZono.prod_unitCol, ConPolyZono.prod_unitCol]
    simp only [hterm]
    rw [← Equiv.sum_comp finProdFinEquiv (fun l : Fin (p₁ * p₂) =>
      γ * (a (Fin.castAdd 2 (Fin.castAdd p₂ (finProdFinEquiv.symm l).1)) ^ 2
        * a (Fin.castAdd 2 (Fin.natAdd p₁ (finProdFinEquiv.symm l).2)) ^ 2))]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  -- the eight groups, split apart along the column layout
  rw [Fin.sum_univ_add (a := 2) (b := p₁ + p₁ + (p₂ + p₂ + (p₁ * p₂ + p₁ * p₂))),
    Fin.sum_univ_add (a := p₁ + p₁) (b := p₂ + p₂ + (p₁ * p₂ + p₁ * p₂)),
    Fin.sum_univ_add (a := p₁) (b := p₁),
    Fin.sum_univ_add (a := p₂ + p₂) (b := p₁ * p₂ + p₁ * p₂),
    Fin.sum_univ_add (a := p₂) (b := p₂),
    Fin.sum_univ_add (a := p₁ * p₂) (b := p₁ * p₂),
    Fin.sum_univ_two]
  simp only [ConPolyZono.unionConCol, ConPolyZono.unionConCoef, Fin.append_left,
    Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one, ConPolyZono.prod_unitCol,
    ConPolyZono.aux_prod_unionWithSel, pow_one, ← mul_assoc]
  -- each group's coefficient pulled out of its sum, and the means read back
  rw [hcross, hcross, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  simp only [ConPolyZono.unionMeanSq]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- The selector rows hold exactly when the factors are in the unit box, `α₁α₂ = 1` and the
selector polynomial vanishes. -/
theorem ConPolyZono.mem_unionUpper_iff {p₁ p₂ : ℕ} (a : Fin (p₁ + p₂ + 2) → ℝ) : -- --- CONCL ---
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
      rw [ConPolyZono.aux_prod_addCol, ConPolyZono.prod_unitCol, ConPolyZono.prod_unitCol,
        pow_one, pow_one] at h
      exact h
    · have h := h₂ 0
      simp only [Matrix.mulVec, dotProduct, PolyZonotope.monomial, Pi.zero_apply, sub_zero] at h
      rw [ConPolyZono.aux_unionCon_value] at h
      exact h
  · rintro ⟨hb, h₁, h₂⟩
    refine ⟨⟨hb, ?_⟩, ?_⟩
    · intro i
      fin_cases i
      simp only [Matrix.mulVec, dotProduct, Finset.univ_unique,
        Fin.default_eq_zero, one_mul, Finset.sum_singleton, PolyZonotope.monomial]
      rw [ConPolyZono.aux_prod_addCol, ConPolyZono.prod_unitCol, ConPolyZono.prod_unitCol,
        pow_one, pow_one, h₁]
    · -- the selector row, at the value `aux_unionCon_value` computes
      intro i
      fin_cases i
      simp only [Matrix.mulVec, dotProduct, PolyZonotope.monomial, Pi.zero_apply, sub_zero]
      rw [ConPolyZono.aux_unionCon_value, h₂]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
