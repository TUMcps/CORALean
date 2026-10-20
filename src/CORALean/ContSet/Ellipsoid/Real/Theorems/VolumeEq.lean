module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Operations.Volume
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# The volume of an ellipsoid

The ellipsoid is `q` plus the image of the unit ball under the square matrix `G = Q^(1/2)`,
so its volume is `|det G|` times the ball's (`Measure.addHaar_image_linearMap`), and
`sqrt(det Q) = sqrt(det(G Gᵀ)) = |det G|`. This is `Ellipsoid.volume` exactly, for every
ellipsoid, degenerate ones included.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

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

/-- The Euclidean unit ball of `Vec ℝ n` has the volume of the unit `n`-ball. -/
theorem Ellipsoid.aux_volume_unitBall : -- --- CONCL ---
    MeasureTheory.volume {u : Vec ℝ n | ‖u‖₂ ≤ 1} =
      ENNReal.ofReal (Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)) := by -- --- PROOF ---
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- no coordinates: one point, of volume `1`
    have hset : {u : Vec ℝ 0 | ‖u‖₂ ≤ 1} = Set.univ := by
      ext u
      simp [norm₂]
    rw [hset, MeasureTheory.volume_pi, Measure.pi_univ]
    simp
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hset : {u : Vec ℝ n | ‖u‖₂ ≤ 1} =
      (WithLp.toLp 2) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_closedBall_zero_iff]
    rw [← norm_toEuclidean]
    rfl
  rw [hset, (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet, EuclideanSpace.volume_closedBall]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
  congr 2
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- The Lebesgue volume of the ellipsoid is CORA's `volume_`, `V_n √det Q`. -/
theorem Ellipsoid.volume_eq (E : Ellipsoid n) : -- --- CONCL ---
    MeasureTheory.volume E.construct = E.volume := by -- --- PROOF ---
  -- the ellipsoid is a translate of the image of the unit ball
  have hcon : E.construct =
      (fun v => -E.q + v) ⁻¹' ((Matrix.toLin' E.G) '' {u : Vec ℝ n | ‖u‖₂ ≤ 1}) := by
    ext x
    simp only [Ellipsoid.construct_eq_sqrt, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, by simp⟩
    · rintro ⟨u, hu, hx⟩
      refine ⟨u, hu, ?_⟩
      have : x = E.q + Matrix.toLin' E.G u := by rw [hx]; abel
      rw [this]
      rfl
  -- translation keeps the volume; the image scales it by `|det G|`
  rw [hcon, measure_preimage_add, Measure.addHaar_image_linearMap,
    Ellipsoid.aux_volume_unitBall, LinearMap.det_toLin']
  unfold Ellipsoid.volume
  rw [← E.G_mul_transpose]
  simp only [Matrix.det_mul, Matrix.det_transpose]
  rw [Real.sqrt_mul_self_eq_abs, ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
