module

public import CORALean.ContSet.ConZonotope.Float.Operations.Compact
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# The float `compact` keeps the set

A dropped generator has every entry of its column of `[G; A; Ae]` certified zero, so no point
and no row reads its coefficient; a dropped equality row has every entry certified zero and `0`
in its interval, so every coefficient vector meets it. A point of the set keeps its kept
coefficients, and a point of the compacted set gets `0` at the dropped ones. Nothing is
rounded, so this is the float set's own equality, not a claim about the exact layer's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum over all of `Fin h` that vanishes off `S` is the sum over the kept indices. -/
theorem ConZonotope.aux_sum_kept {h : ℕ} (S : Finset (Fin h)) (f : Fin h → ℝ)
    (hf : ∀ j, j ∉ S → f j = 0) :
    ∑ j, f j = ∑ l : Fin S.card, f (S.orderEmbOfFin rfl l) := by
  rw [← Finset.sum_subset (Finset.subset_univ S) fun j _ hj => hf j hj,
    ← Finset.sum_coe_sort S f]
  refine (Equiv.sum_comp (S.orderIsoOfFin rfl).toEquiv fun x => f x).symm.trans ?_
  exact Finset.sum_congr rfl fun l _ => by rw [← Finset.coe_orderIsoOfFin_apply]; rfl

/-- A certified zero is zero. -/
theorem ConZonotope.aux_toReal_eq_zero {a : 𝕋}
    (h : (le a (FloatOps.zero : 𝕋) && le (FloatOps.zero : 𝕋) a) = true) :
    toReal a = 0 := by -- --- PROOF ---
  rw [Bool.and_eq_true] at h
  have h₁ := toReal_le_of_le h.1
  have h₂ := toReal_le_of_le h.2
  rw [toReal_zero] at h₁ h₂
  exact le_antisymm h₁ h₂


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.compact_exact (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.compact.construct = cZ.construct := by -- --- PROOF ---
  set S : Finset (Fin cZ.h) := Finset.univ.filter fun j : Fin cZ.h =>
    !((List.finRange n).all (fun i => le (cZ.G j i) FloatOps.zero
        && le FloatOps.zero (cZ.G j i))
      && (List.finRange cZ.P.m).all (fun k => le (cZ.P.A k j) FloatOps.zero
        && le FloatOps.zero (cZ.P.A k j))
      && (List.finRange cZ.P.me).all (fun k => le (cZ.P.Ae k j) FloatOps.zero
        && le FloatOps.zero (cZ.P.Ae k j)))
    with hS
  set R : Finset (Fin cZ.P.me) := Finset.univ.filter fun r : Fin cZ.P.me =>
    !((List.finRange cZ.h).all (fun j => le (cZ.P.Ae r j) FloatOps.zero
        && le FloatOps.zero (cZ.P.Ae r j))
      && le (cZ.P.be.inf r) FloatOps.zero && le FloatOps.zero (cZ.P.be.sup r)) with hR
  -- what a dropped generator is: zero, and read by no row
  have hdrop : ∀ j, j ∉ S → (∀ i, toReal (cZ.G j i) = 0) ∧ (∀ k, toReal (cZ.P.A k j) = 0)
      ∧ ∀ k, toReal (cZ.P.Ae k j) = 0 := by
    intro j hj
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true',
      Bool.not_eq_false, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      forall_const] at hj
    exact ⟨fun i => ConZonotope.aux_toReal_eq_zero (by simpa using hj.1.1 i),
      fun k => ConZonotope.aux_toReal_eq_zero (by simpa using hj.1.2 k),
      fun k => ConZonotope.aux_toReal_eq_zero (by simpa using hj.2 k)⟩
  -- what a dropped equality row is: zero, with `0` in its interval
  have hrow : ∀ r, r ∉ R → (∀ j, toReal (cZ.P.Ae r j) = 0)
      ∧ toReal (cZ.P.be.inf r) ≤ 0 ∧ 0 ≤ toReal (cZ.P.be.sup r) := by
    intro r hr
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true',
      Bool.not_eq_false, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      forall_const] at hr
    refine ⟨fun j => ConZonotope.aux_toReal_eq_zero (by simpa using hr.1.1 j), ?_, ?_⟩
    · simpa [toReal_zero] using toReal_le_of_le hr.1.2
    · simpa [toReal_zero] using toReal_le_of_le hr.2
  show nominalSet cZ.compact + cZ.E.construct = nominalSet cZ + cZ.E.construct
  congr 1
  ext y
  rw [ConZonotope.mem_nominalSet_iff, ConZonotope.mem_nominalSet_iff]
  constructor
  · -- the dropped coefficients set to zero
    rintro ⟨ξ', hξ', hP', hy⟩
    obtain ⟨hin', heq'⟩ := HPolytope.mem_construct_iff.mp hP'
    set ξ : Vec ℝ cZ.h := fun j =>
      if h : j ∈ S then ξ' ((S.orderIsoOfFin rfl).symm ⟨j, h⟩) else 0 with hξdef
    have hξe : ∀ l, ξ (S.orderEmbOfFin rfl l) = ξ' l := by
      intro l
      have hm : S.orderEmbOfFin rfl l ∈ S := Finset.orderEmbOfFin_mem S rfl l
      have hl : (S.orderIsoOfFin rfl).symm ⟨S.orderEmbOfFin rfl l, hm⟩ = l := by
        rw [OrderIso.symm_apply_eq]
        exact Subtype.ext (Finset.coe_orderIsoOfFin_apply S rfl l).symm
      simp only [hξdef, hm, dite_true]
      exact congrArg ξ' hl
    have hoff : ∀ j, j ∉ S → ξ j = 0 := fun j hj => by simp [hξdef, hj]
    -- a sum against `ξ` is the compacted one against `ξ'`
    have hsum : ∀ g : Fin cZ.h → ℝ, ∑ j, g j * ξ j
        = ∑ l : Fin S.card, g (S.orderEmbOfFin rfl l) * ξ' l := fun g => by
      rw [ConZonotope.aux_sum_kept S _ fun j hj => by rw [hoff j hj, mul_zero]]
      exact Finset.sum_congr rfl fun l _ => by rw [hξe]
    refine ⟨ξ, fun j => ?_, HPolytope.mem_construct_iff.mpr ⟨fun k => ?_, fun r => ?_⟩,
      fun i => ?_⟩
    · by_cases hj : j ∈ S
      · simp only [hξdef, hj, dite_true]; exact hξ' _
      · rw [hoff j hj, abs_zero]; exact zero_le_one
    · have := hin' k
      simp only [mulVec, dotProduct, toRealMat] at this ⊢
      rw [hsum]
      exact this
    · by_cases hr : r ∈ R
      · -- a kept row is the compacted set's own
        obtain ⟨r', hr'⟩ : ∃ r', R.orderEmbOfFin rfl r' = r :=
          ⟨(R.orderIsoOfFin rfl).symm ⟨r, hr⟩, by
            rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]⟩
        have := heq' r'
        subst hr'
        simp only [mulVec, dotProduct, toRealMat] at this ⊢
        rw [hsum]
        exact this
      · -- a dropped row is `0 x ∈ be` with `0 ∈ be`
        obtain ⟨hz, hlo, hhi⟩ := hrow r hr
        have : (toRealMat cZ.P.Ae *ᵥ ξ) r = 0 := by
          simp only [mulVec, dotProduct, toRealMat]
          exact Finset.sum_eq_zero fun j _ => by rw [hz j, zero_mul]
        rw [this]
        exact ⟨hlo, hhi⟩
    · rw [hy i, hsum]
      rfl
  · -- the kept coefficients
    rintro ⟨ξ, hξ, hP, hy⟩
    obtain ⟨hin, heq⟩ := HPolytope.mem_construct_iff.mp hP
    have hsum : ∀ g : Fin cZ.h → ℝ, (∀ j, j ∉ S → g j = 0) → ∑ j, g j * ξ j
        = ∑ l : Fin S.card, g (S.orderEmbOfFin rfl l) * ξ (S.orderEmbOfFin rfl l) :=
      fun g hg => ConZonotope.aux_sum_kept S _ fun j hj => by rw [hg j hj, zero_mul]
    refine ⟨fun l => ξ (S.orderEmbOfFin rfl l), fun l => hξ _,
      HPolytope.mem_construct_iff.mpr ⟨fun k => ?_, fun r => ?_⟩, fun i => ?_⟩
    -- each row reads only the kept coefficients
    · have := hin k
      simp only [mulVec, dotProduct, toRealMat] at this
      show ∑ l : Fin S.card, toReal (cZ.P.A k (S.orderEmbOfFin rfl l))
        * ξ (S.orderEmbOfFin rfl l) ≤ toReal (cZ.P.b k)
      rw [← hsum _ fun j hj => (hdrop j hj).2.1 k]
      exact this
    · have := heq (R.orderEmbOfFin rfl r)
      simp only [mulVec, dotProduct, toRealMat] at this
      show toReal (cZ.P.be.inf (R.orderEmbOfFin rfl r)) ≤ ∑ l : Fin S.card,
          toReal (cZ.P.Ae (R.orderEmbOfFin rfl r) (S.orderEmbOfFin rfl l))
            * ξ (S.orderEmbOfFin rfl l)
        ∧ ∑ l : Fin S.card, toReal (cZ.P.Ae (R.orderEmbOfFin rfl r) (S.orderEmbOfFin rfl l))
            * ξ (S.orderEmbOfFin rfl l) ≤ toReal (cZ.P.be.sup (R.orderEmbOfFin rfl r))
      rw [← hsum _ fun j hj => (hdrop j hj).2.2 _]
      exact this
    · rw [hy i, hsum _ fun j hj => (hdrop j hj).1 i]
      rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
