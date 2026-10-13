import CORALean.ContSet.Zonotope.Real.Operations.Rank
import CORALean.ContSet.Zonotope.Real.Operations.Volume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A zonotope of rank below `n` has volume zero

It lies in the translate of the span of its generators, a proper subspace, which has Haar
measure zero (`Measure.addHaar_submodule`). The `n`-subsets' determinants all vanish too: `n`
generators of a rank-`< n` family are dependent, so `Zonotope.volume` is `0` as well, which is
CORA's early `vol = 0` return for `rank(G) < n` (and, as the rank is at most the count, for
fewer than `n` generators).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A rank below `n` says the generators do not span the space. -/
theorem Zonotope.aux_span_ne_top (Z : Zonotope (Vec ℝ n)) (hr : Z.rank < n) :
    Submodule.span ℝ (Set.range Z.G) ≠ ⊤ := by -- --- PROOF ---
  intro h
  have : Z.rank = n := by
    unfold Zonotope.rank
    rw [h, finrank_top, Module.finrank_fin_fun]
  omega

/-- `n` generators with an invertible matrix span the space. -/
theorem Zonotope.aux_det_eq_zero (Z : Zonotope (Vec ℝ n)) (hr : Z.rank < n) {q : ℕ}
    (e : Fin n → Fin q) (G : Fin q → Vec ℝ n) (hG : Set.range G ⊆ Set.range Z.G) :
    (Matrix.of fun i k => G (e k) i : Mat ℝ n n).det = 0 := by -- --- PROOF ---
  by_contra hdet
  set M : Mat ℝ n n := Matrix.of fun i k => G (e k) i with hM
  apply Z.aux_span_ne_top hr
  rw [eq_top_iff]
  intro v _
  -- `v = M (M⁻¹ v)` is a combination of the columns of `M`
  have hv : v = M *ᵥ (M⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have : M *ᵥ (M⁻¹ *ᵥ v) = ∑ k, (M⁻¹ *ᵥ v) k • G (e k) := by
    ext i
    simp [hM, Matrix.mulVec, dotProduct, mul_comm, Finset.sum_apply]
  rw [hv, this]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hG ⟨e k, rfl⟩))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.volume_eq_of_rank_lt (Z : Zonotope (Vec ℝ n)) (hr : Z.rank < n) :
    MeasureTheory.volume Z.construct = Z.volume := by -- --- PROOF ---
  have h0 : Z.volume = 0 := by
    unfold Zonotope.volume
    rw [ENNReal.ofReal_eq_zero]
    refine le_of_eq ?_
    rw [Finset.sum_eq_zero, mul_zero]
    intro S _
    by_cases hS : S.card = n
    · rw [dif_pos hS, abs_eq_zero]
      exact Z.aux_det_eq_zero hr (fun k => S.orderEmbOfFin hS k) Z.G subset_rfl
    · rw [dif_neg hS]
  rw [h0]
  -- inside the translate of the span of the generators
  refine measure_mono_null (t := (fun v => -Z.c + v) ⁻¹'
    (Submodule.span ℝ (Set.range Z.G) : Set (Vec ℝ n))) ?_ ?_
  · rintro x ⟨β, -, rfl⟩
    simp only [Set.mem_preimage, neg_add_cancel_left, SetLike.mem_coe]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [measure_preimage_add]
    exact Measure.addHaar_submodule _ _ (Z.aux_span_ne_top hr)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
