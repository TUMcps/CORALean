module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Operations.Volume
public import CORALean.ContSet.Ellipsoid.Real.Operations.Rank
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# A rank-deficient ellipsoid has volume zero

With `rank Q < n`, `det Q = 0`, so `Ellipsoid.volume` is `0`; and the ellipsoid lies in the
translate of the range of `G = Q^(1/2)`, which has the rank of `G Gᵀ = Q`
(`Matrix.rank_self_mul_transpose`), a proper subspace and so of Haar measure zero
(`Measure.addHaar_submodule`).

## Inputs
* `E` – ellipsoid

## Hypotheses
* `hr` – rank below `n`

## Conclusion
* the Lebesgue volume of `E` is `volume E`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Ellipsoid.aux_det_shape_eq_zero (E : Ellipsoid n)
    (hr : E.rank < n) : -- --- CONCL ---
    E.Q.det = 0 := by -- --- PROOF ---
  by_contra hdet
  have hu : IsUnit E.Q := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have := Matrix.rank_of_isUnit E.Q hu
  rw [Fintype.card_fin] at this
  change E.Q.rank < n at hr
  omega


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.volume_eq_of_rank_lt (E : Ellipsoid n) (hr : E.rank < n) : -- --- CONCL ---
    MeasureTheory.volume E.construct = E.volume := by -- --- PROOF ---
  -- the ellipsoid as `q + G u`, `‖u‖₂ ≤ 1`
  simp only [Ellipsoid.construct_eq_sqrt] at *
  have h0 : E.volume = 0 := by
    unfold Ellipsoid.volume
    simp only [E.aux_det_shape_eq_zero hr, Real.sqrt_zero, mul_zero, ENNReal.ofReal_zero]
  rw [h0]
  -- `G` is not onto, so its range is a proper subspace, of measure zero
  have hne : LinearMap.range (Matrix.mulVecLin E.G) ≠ ⊤ := by
    intro h
    have : E.rank = n := by
      unfold Ellipsoid.rank
      rw [← E.G_mul_transpose, Matrix.rank_self_mul_transpose]
      unfold Matrix.rank
      rw [h, finrank_top, Module.finrank_fin_fun]
    omega
  refine measure_mono_null (t := (fun v => -E.q + v) ⁻¹'
    (LinearMap.range (Matrix.mulVecLin E.G) : Set (Vec ℝ n))) ?_ ?_
  · rintro x ⟨u, -, rfl⟩
    simp only [Set.mem_preimage, neg_add_cancel_left, SetLike.mem_coe]
    exact ⟨u, rfl⟩
  · rw [measure_preimage_add]
    exact Measure.addHaar_submodule _ _ hne

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
