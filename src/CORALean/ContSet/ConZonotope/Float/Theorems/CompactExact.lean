module

public import CORALean.ContSet.ConZonotope.Float.Operations.Compact
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Theorems.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.DropZerosExact
public import CORALean.ContSet.HPolytope.Float.Theorems.MemSelectColsNominalIff

@[expose] public section

/-!
# The float `compact` keeps the set

A dropped generator has every entry of its column of `[G; A; Ae]` certified zero, so no point
and no row reads its coefficient: the rows read a coefficient vector through the kept columns
alone, which is what `HPolytope.mem_selectCols_nominal_iff` asks, and the zero rows go without
changing the set (`HPolytope.dropZeros_exact`). A point of the set keeps its kept coefficients,
and a point of the compacted set gets `0` at the dropped ones. Nothing is rounded, so this is the
float set's own equality, not a claim about the exact layer's.

## Inputs
* `cZ` – float constrained zonotope

## Hypotheses
* none

## Conclusion
* compacting leaves the set unchanged
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum over all of `Fin h` that vanishes off `S` is the sum over the kept indices. -/
private theorem ConZonotope.aux_sum_kept {h : ℕ} (S : Finset (Fin h)) (f : Fin h → ℝ)
    (hf : ∀ j, j ∉ S → f j = 0) :
    ∑ j, f j = ∑ l : Fin S.card, f (S.orderEmbOfFin rfl l) := by
  rw [← Finset.sum_subset (Finset.subset_univ S) fun j _ hj => hf j hj,
    ← Finset.sum_coe_sort S f]
  refine (Equiv.sum_comp (S.orderIsoOfFin rfl).toEquiv fun x => f x).symm.trans ?_
  exact Finset.sum_congr rfl fun l _ => by rw [← Finset.coe_orderIsoOfFin_apply]; rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.compact_exact (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    cZ.compact.construct = cZ.construct := by -- --- PROOF ---
  set S : Finset (Fin cZ.h) := Finset.univ.filter fun j : Fin cZ.h =>
    !(HPolytope.isZeroVec (cZ.G j) && cZ.P.isZeroCol j) with hS
  set sel : Fin S.card → Fin cZ.h := ⇑(S.orderEmbOfFin rfl) with hsel
  -- what a dropped generator is: zero, and read by no row
  have hdrop : ∀ j, j ∉ S → (∀ i, toReal (cZ.G j i) = 0) ∧ (∀ k, toReal (cZ.P.A k j) = 0)
      ∧ ∀ k, toReal (cZ.P.Ae k j) = 0 := by
    intro j hj
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true',
      Bool.not_eq_false, Bool.and_eq_true, HPolytope.isZeroVec, HPolytope.isZeroCol,
      List.all_eq_true, List.mem_finRange, true_implies] at hj
    have hz : ∀ {a : 𝕋}, HPolytope.eqScalar a FloatOps.zero = true → toReal a = 0 :=
      fun h => (HPolytope.toReal_eq_of_eqScalar h).trans toReal_zero
    exact ⟨fun i => hz (hj.1 i), fun k => hz (hj.2.1 k), fun k => hz (hj.2.2 k)⟩
  -- the zero rows go without changing the nominal part, the box being the origin
  have hkey : ∀ ξ' : Vec ℝ S.card, ξ' ∈ cZ.compact.P.nominal.construct
      ↔ ξ' ∈ (cZ.P.selectCols sel).nominal.construct := fun ξ' => by
    have hI : (cZ.P.selectCols sel).dropZeros.I_error = Interval.origin S.card := by
      unfold HPolytope.dropZeros
      split <;> rfl
    show ξ' ∈ (cZ.P.selectCols sel).dropZeros.nominal.construct ↔ _
    rw [← HPolytope.mem_nominal_of_origin hI, HPolytope.dropZeros_exact,
      HPolytope.mem_nominal_of_origin rfl]
  -- a sum that vanishes off `S` is the sum over the kept indices
  have hsum : ∀ g : Fin cZ.h → ℝ, (∀ j, j ∉ S → g j = 0) → ∑ j, g j = ∑ l, g (sel l) :=
    fun g hg => ConZonotope.aux_sum_kept S g hg
  show nominalSet cZ.compact + cZ.I_error.construct = nominalSet cZ + cZ.I_error.construct
  congr 1
  ext y
  rw [ConZonotope.mem_nominalSet_iff, ConZonotope.mem_nominalSet_iff]
  constructor
  · -- the dropped coefficients set to zero
    rintro ⟨ξ', hξ', hP', hy⟩
    set ξ : Vec ℝ cZ.h := fun j =>
      if h : j ∈ S then ξ' ((S.orderIsoOfFin rfl).symm ⟨j, h⟩) else 0 with hξdef
    -- `ξ` reads `ξ'` back at the kept coefficients
    have hξe : ∀ l, ξ (sel l) = ξ' l := by
      intro l
      have hm : S.orderEmbOfFin rfl l ∈ S := Finset.orderEmbOfFin_mem S rfl l
      have hl : (S.orderIsoOfFin rfl).symm ⟨S.orderEmbOfFin rfl l, hm⟩ = l := by
        rw [OrderIso.symm_apply_eq]
        exact Subtype.ext (Finset.coe_orderIsoOfFin_apply S rfl l).symm
      simp only [hξdef, hsel, hm, dite_true]
      exact congrArg ξ' hl
    have hoff : ∀ j, j ∉ S → ξ j = 0 := fun j hj => by simp [hξdef, hj]
    have hrow : ∀ {k : ℕ} (M : Mat 𝕋 k cZ.h) (i : Fin k),
        (toRealMat M *ᵥ ξ) i = ∑ l, toReal (M i (sel l)) * ξ (sel l) := fun M i =>
      hsum _ fun j hj => by rw [hoff j hj, mul_zero]
    -- the compacted rows at `ξ'` are the rows at `ξ`
    have hξ'e : ξ' = fun l => ξ (sel l) := funext fun l => (hξe l).symm
    have hP'' := (hkey ξ').mp hP'
    rw [hξ'e, HPolytope.mem_selectCols_nominal_iff _ _ (hrow _) (hrow _)] at hP''
    refine ⟨ξ, fun j => ?_, hP'', fun i => ?_⟩
    · by_cases hj : j ∈ S
      · simp only [hξdef, hj, dite_true]; exact hξ' _
      · rw [hoff j hj, abs_zero]; exact zero_le_one
    · rw [hy i, hsum _ fun j hj => by rw [hoff j hj, mul_zero]]
      exact congrArg (toReal (cZ.c i) + ·) (Finset.sum_congr rfl fun l _ => by
        show toReal (cZ.G (sel l) i) * ξ' l = toReal (cZ.G (sel l) i) * ξ (sel l)
        rw [hξe])
  · -- the kept coefficients
    rintro ⟨ξ, hξ, hP, hy⟩
    have hrow : ∀ {k : ℕ} (M : Mat 𝕋 k cZ.h), (∀ i j, j ∉ S → toReal (M i j) = 0) →
        ∀ i, (toRealMat M *ᵥ ξ) i = ∑ l, toReal (M i (sel l)) * ξ (sel l) := fun M hM i =>
      hsum _ fun j hj => by show toReal (M i j) * ξ j = 0; rw [hM i j hj, zero_mul]
    refine ⟨fun l => ξ (sel l), fun l => hξ _, (hkey _).mpr
      ((HPolytope.mem_selectCols_nominal_iff _ _
        (hrow _ fun k j hj => (hdrop j hj).2.1 k) (hrow _ fun k j hj => (hdrop j hj).2.2 k)).mpr
        hP), fun i => ?_⟩
    rw [hy i, hsum _ fun j hj => by rw [(hdrop j hj).1 i, zero_mul]]
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
