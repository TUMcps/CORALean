module

public import CORALean.ContSet.PolyZonotope.Float.Operations.BoxOut
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.BoxOutOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne

@[expose] public section

/-!
# Boxing out generators encloses, in float

Any choice of removed dependent and taken independent generators gives an enclosure: the removed
generators reach at most the sum of their absolute values in a coordinate, the box radius is
that sum rounded up and the taken independent ones only widen it, so one coefficient per coordinate
in `[-1, 1]` reproduces what they contributed; the kept columns, the center and the error box are
as before.

## Inputs
* `pZ` – polynomial zonotope
* `removed` – mask of dependent generators removed
* `taken` – mask of independent generators taken

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.boxOut_outer (pZ : PolyZonotope (Vec 𝕋 n)) (removed : Fin pZ.h → Bool)
    (taken : Fin pZ.q → Bool) : -- --- CONCL ---
    pZ.construct ⊆ (pZ.boxOut removed taken).construct := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hy⟩ := PolyZonotope.mem_nominalSet_iff.mp hy
  -- the removed generators reach `D i` in coordinate `i`, the box has radius `R i`
  set D : Fin n → ℝ := fun i => ∑ l, if removed l then
    toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l else 0 with hD
  set R : Fin n → ℝ := fun i => toReal (pZ.step_boxOutRadius removed taken i) with hR
  have hbound : ∀ i, |D i| ≤ R i := fun i => by
    -- the removed generators reach at most their absolute sum, which the radius rounds up
    have h1 : |D i| ≤ ∑ l, if removed l then |toReal (pZ.G l i)| else 0 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      by_cases hl : removed l = true
      · simp only [hl, if_true, abs_mul]
        simpa using mul_le_mul_of_nonneg_left
          (Real.PolyZonotope.abs_monomial_le_one pZ.E ha l) (abs_nonneg (toReal (pZ.G l i)))
      · simp [hl]
    have h2 : (∑ l, if removed l then |toReal (pZ.G l i)| else 0) ≤
        toReal (sumUp fun l => if removed l then absolute (pZ.G l i) else zero) :=
      le_trans (Finset.sum_le_sum fun l _ => by
        by_cases hl : removed l = true <;> simp [hl, toReal_absolute, toReal_zero]) (sum_le_sumUp _)
    have h3 : 0 ≤ toReal (sumUp fun j => if taken j then absolute (pZ.GI j i) else zero) :=
      le_trans (Finset.sum_nonneg fun j _ => by
        by_cases hj : taken j = true <;> simp [hj, toReal_absolute, toReal_zero]) (sum_le_sumUp _)
    exact h1.trans (h2.trans (by
      have := add_le_addUp (sumUp fun l => if removed l then absolute (pZ.G l i) else zero)
        (sumUp fun j => if taken j then absolute (pZ.GI j i) else zero)
      show _ ≤ toReal (addUp _ _)
      linarith))
  have hnonneg : ∀ i, (0 : ℝ) ≤ R i := fun i => (abs_nonneg _).trans (hbound i)
  -- the kept columns, read through the order isomorphism
  set keep := Finset.univ.filter fun l => removed l = false with hkeep
  have hK : ∀ (i : Fin n), (∑ l' : Fin keep.card, toReal (pZ.G (keep.orderEmbOfFin rfl l') i)
      * Real.PolyZonotope.monomial pZ.E a (keep.orderEmbOfFin rfl l'))
      = ∑ l, if removed l then 0 else toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l := by
    intro i
    let f : Fin pZ.h → ℝ := fun l => toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l
    have h1 : (∑ l' : Fin keep.card, f (keep.orderEmbOfFin rfl l')) = ∑ x : keep, f x :=
      Equiv.sum_comp (keep.orderIsoOfFin rfl).toEquiv fun x : keep => f x
    have h2 : (∑ x : keep, f x) = ∑ l ∈ keep, f l := Finset.sum_coe_sort keep f
    have h3 : (∑ l ∈ keep, f l) = ∑ l, if removed l then 0 else f l := by
      rw [hkeep, Finset.sum_filter]
      exact Finset.sum_congr rfl fun l _ => by cases removed l <;> simp
    exact h1.trans (h2.trans h3)
  -- the same factors, the same coefficients, and one coefficient per coordinate for the box
  set β' : Fin (pZ.q + n) → ℝ := Fin.append β (fun i => Real.Zonotope.coefficient (R i) (D i))
    with hβ'
  have hβ'le : ∀ j, |β' j| ≤ 1 := by
    refine Fin.addCases (fun j => ?_) (fun i => ?_)
    · simpa [hβ'] using hβ j
    · simpa [hβ'] using Real.Zonotope.abs_coefficient_le_one (hnonneg i) (hbound i)
  refine ⟨fun i => toReal ((pZ.boxOut removed taken).c i)
      + (∑ l, toReal ((pZ.boxOut removed taken).G l i)
          * Real.PolyZonotope.monomial (pZ.boxOut removed taken).E a l)
      + ∑ j, toReal ((pZ.boxOut removed taken).GI j i) * β' j,
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β', ha, hβ'le, fun _ => rfl⟩, e, he, ?_⟩
  funext i
  -- the box reproduces what the removed generators reached
  have hdiag : (∑ j, toReal ((pZ.boxOut removed taken).GI j i) * β' j)
      = (∑ j, toReal (pZ.GI j i) * β j) + R i * Real.Zonotope.coefficient (R i) (D i) := by
    refine (Fin.sum_univ_add (a := pZ.q) (b := n)
      (fun j : Fin (pZ.q + n) => toReal ((pZ.boxOut removed taken).GI j i) * β' j)).trans ?_
    simp only [PolyZonotope.boxOut, Fin.append_left, Fin.append_right, hβ', toReal_diagonalBlock]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp [hR, toRealVec]
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_mul]
    · exact fun h => absurd (Finset.mem_univ i) h
  -- the sum over all columns splits into the kept ones and the removed ones
  have hsplit : (∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
      = (∑ l, if removed l then 0 else toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
        + D i := by
    rw [hD, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by cases removed l <;> simp
  show _ + _ + _ + e i = y i + e i
  rw [hdiag, Real.Zonotope.mul_coefficient (hbound i), hy i, hsplit]
  have hG : (∑ l, toReal ((pZ.boxOut removed taken).G l i)
      * Real.PolyZonotope.monomial (pZ.boxOut removed taken).E a l) = _ := hK i
  have hc : toReal ((pZ.boxOut removed taken).c i) = toReal (pZ.c i) := rfl
  rw [hG, hc]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
