module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Volume
public import CORALean.ContSet.Ellipsoid.Real.Theorems.RankShape
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# A rank-deficient ellipsoid has volume zero

With `rank G < n` the ellipsoid lies in the translate of the range of `G`, a proper subspace,
which has Haar measure zero (`Measure.addHaar_submodule`); and `det(G Gᵀ) = 0`, as `G Gᵀ` has
the rank of `G` (`Ellipsoid.rank_shape`), so `Ellipsoid.volume` is `0` too. For every `k`.
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

theorem Ellipsoid.aux_det_shape_eq_zero (E : Ellipsoid n) (hr : E.rank < n) :
    E.shape.det = 0 := by -- --- PROOF ---
  by_contra hdet
  have hu : IsUnit E.shape := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have := Matrix.rank_of_isUnit E.shape hu
  rw [Ellipsoid.rank_shape, Fintype.card_fin] at this
  omega


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.volume_eq_of_rank_lt (E : Ellipsoid n) (hr : E.rank < n) :
    MeasureTheory.volume E.construct = E.volume := by -- --- PROOF ---
  have h0 : E.volume = 0 := by
    unfold Ellipsoid.volume
    simp only [E.aux_det_shape_eq_zero hr, Real.sqrt_zero, mul_zero, ENNReal.ofReal_zero]
  rw [h0]
  have hne : LinearMap.range (Matrix.mulVecLin E.G) ≠ ⊤ := by
    intro h
    have : E.rank = n := by
      unfold Ellipsoid.rank Matrix.rank
      rw [h, finrank_top, Module.finrank_fin_fun]
    omega
  refine measure_mono_null (t := (fun v => -E.c + v) ⁻¹'
    (LinearMap.range (Matrix.mulVecLin E.G) : Set (Vec ℝ n))) ?_ ?_
  · rintro x ⟨u, -, rfl⟩
    simp only [Set.mem_preimage, neg_add_cancel_left, SetLike.mem_coe]
    exact ⟨u, rfl⟩
  · rw [measure_preimage_add]
    exact Measure.addHaar_submodule _ _ hne

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
