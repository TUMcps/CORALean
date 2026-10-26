module

public import CORALean.ContSet.ProbZonotope.Real.Theorems.PyramidOuter
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# `pyramid` alone is not an upper bound of the probability

`pyramid_outer` needs the floor `maxVal(1) · V(Q)`. Without it the value CORA returns can be far
below the probability: in `ℝ¹` take the law `N(0, 1)` (the mean zonotope is the point `0`, the
covariance `1`), `mArray` the single value `1` and the polytope `Q = ℝ`. The set has probability
`1`, and
`pyramid = (maxVal(2) - maxVal(1)) · V(zonotope(probZ, 1))` is the density step from the
`1`-sigma bound to the peak times the length `2` of `[-1, 1]`, which is below `1`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* `pyramid` alone is not an upper bound of the probability
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory WithLp Matrix
open scoped _root_.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The single value `1` of `mArray`. -/
def aux_one : Fin 1 → ℝ := fun _ => 1

/-- The point `0` with covariance `1` in `ℝ¹`. -/
private def aux_stdNormal : ProbZonotope 1 := ⟨⟨0, 0, Fin.elim0⟩, 1⟩

private theorem aux_stdNormal_zonotope_subset : -- --- CONCL ---
    (aux_stdNormal.zonotope 1).construct ⊆ {y | |y 0| ≤ 1} := by -- --- PROOF ---
  rw [ProbZonotope.zonotope, ← Zonotope.plus_exact]
  rintro _ ⟨a, ha, b, ⟨β, hβ, rfl⟩, rfl⟩
  obtain ⟨β0, -, rfl⟩ := ha
  simp only [aux_stdNormal, confidenceZonotope, CFC.sqrt_one] at *
  simpa using hβ 0

private theorem aux_stdNormal_volume_le : -- --- CONCL ---
    let P := (toLp 2 '' (aux_stdNormal.zonotope 1).construct : Set (EuclideanSpace ℝ (Fin 1)))
    volume.real P ≤ 2 := by -- --- PROOF ---
  intro P
  have hsub : P
      ⊆ ofLp ⁻¹' Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 1) := by
    rintro _ ⟨y, hy, rfl⟩
    have := aux_stdNormal_zonotope_subset hy
    simp only [Set.mem_setOf_eq, abs_le] at this
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> obtain rfl : i = 0 := Subsingleton.elim _ _
    · simpa using this.1
    · simpa using this.2
  have hvol : volume (ofLp ⁻¹' Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 1) :
      Set (EuclideanSpace ℝ (Fin 1))) = ENNReal.ofReal 2 := by
    rw [(PiLp.volume_preserving_ofLp (Fin 1)).measure_preimage
      measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    simp; norm_num
  have hfin : volume P ≤ ENNReal.ofReal 2 := (measure_mono hsub).trans hvol.le
  calc _ ≤ (ENNReal.ofReal 2).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
    _ = 2 := ENNReal.toReal_ofReal (by norm_num)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.pyramid_not_ge_prob : -- --- CONCL ---
    ∃ (P : ProbZonotope 1) (ν : Measure (EuclideanSpace ℝ (Fin 1))), ν ∈ P.laws ∧
      ν Set.univ = 1 ∧ P.pyramid aux_one Set.univ < 1 := by -- --- PROOF ---
  refine ⟨aux_stdNormal, multivariateGaussian (toLp 2 0) 1,
    ⟨0, ⟨fun _ => 0, fun j => by simp, by simp [aux_stdNormal]⟩, rfl⟩, measure_univ, ?_⟩
  -- the peak `K = (2π)^{-1/2}` is at most `1/2`
  have hπ : (2 : ℝ) ≤ (2 * π) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_three])
  set K : ℝ := 1 / (2 * π) ^ ((1 : ℝ) / 2) with hK
  have hK0 : 0 < K := by have : 0 < 2 * π := by positivity
                         positivity
  have hK1 : K ≤ 1 / 2 := by
    rw [hK, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  -- the density on the `m`-sigma bound, and the two levels of the single layer
  have hmax : ∀ m : ℝ, aux_stdNormal.max m = K * Real.exp (-(1 / 2) * m ^ 2) := fun m => by
    simp [ProbZonotope.max, aux_stdNormal, hK]
  have hV := aux_stdNormal_volume_le
  have hE : 0 < Real.exp (-(1 / 2 : ℝ)) ∧ Real.exp (-(1 / 2 : ℝ)) ≤ 1 :=
    ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (by norm_num)⟩
  have hlo : aux_stdNormal.pyramidLevels aux_one (0 : Fin 1).castSucc
      = K * Real.exp (-(1 / 2)) := by
    rw [ProbZonotope.pyramidLevels, Fin.snoc_castSucc]
    simp [hmax, aux_one]
  have hhi : aux_stdNormal.pyramidLevels aux_one (0 : Fin 1).succ = K := by
    have : aux_stdNormal.pyramidLevels aux_one (0 : Fin 1).succ = aux_stdNormal.max 0 :=
      Fin.snoc_last (α := fun _ => ℝ) _ _
    rw [this, hmax]
    simp
  have hpy : aux_stdNormal.pyramid aux_one Set.univ
      = (K - K * Real.exp (-(1 / 2))) * volume.real
        (toLp 2 '' (aux_stdNormal.zonotope 1).construct : Set (EuclideanSpace ℝ (Fin 1))) := by
    simp only [ProbZonotope.pyramid, Fin.sum_univ_one, hlo, hhi, Set.inter_univ, aux_one]
  -- the volume is at most `2`, the step at most `K (1 - e^{-1/2}) < 1/2`
  rw [hpy]
  have hstep : 0 ≤ K - K * Real.exp (-(1 / 2)) := by nlinarith
  calc _ ≤ (K - K * Real.exp (-(1 / 2))) * 2 := mul_le_mul_of_nonneg_left hV hstep
    _ < 1 := by nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
