module

public import CORALean.ContDynamics.LinearSys.Theorems.GirardExampleSpec
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# [1, Lemma 2]'s convergence bound, as printed, is false

[1, Lemma 2] states
`d_H(R_[0,r](Z), P + □(α_r + β_r)) ≤ r‖A‖e^{r‖A‖}(µ/‖A‖ + (1/2 + r) sup_{x∈Z} ‖x‖)`. At
`x' = 100x + u`, `‖u‖ ≤ µ = 0`, `Z = [0, 2]`, `r = 1/100` (`girardExample_spec`) the right side is
`1.02e ≈ 2.77` and the distance is at least `3e - 5 ≈ 3.15`. Every hypothesis of the lemma holds:
`r > 0`, `µ ≥ 0`, `Z` a zonotope; [1] assumes nothing about `r‖A‖`, `Z` or the origin. The sets
compared are the lemma's own: the union of `Φ_t(Z)` over `[0, r]` and `P + □(α_r + β_r)` with `P` of
eq. 5 of [1]. `hausdorffDist_iUnion_reachSetExact_linComb_plus_cube_le` is the corrected bound, with
`(1/2 + r‖A‖)`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed convergence bound is exceeded by an example meeting every hypothesis

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". Hybrid Systems:
      Computation and Control, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2], convergence, as printed, fails: a system, a zonotope and a step meeting
every hypothesis where the distance exceeds `r‖A‖e^{r‖A‖}(µ/‖A‖ + (1/2 + r) sup ‖x‖)`. -/
theorem LinearSys.exists_lt_hausdorffDist_iUnion_reachSetExact : -- --- CONCL ---
    ∃ (sys : LinearSys ℝ 1) (Z U : Zonotope (Vec ℝ 1)) (μ r s : ℝ),
      0 < ‖toRealMat sys.A‖ ∧ 0 < r ∧ 0 ≤ μ ∧ U.construct = Metric.closedBall 0 μ
      ∧ IsGreatest ((fun x => ‖x‖) '' Z.construct) s
      ∧ r * ‖toRealMat sys.A‖ * Real.exp (r * ‖toRealMat sys.A‖)
            * (μ / ‖toRealMat sys.A‖ + (1 / 2 + r) * s)
        < Metric.hausdorffDist
          (⋃ t ∈ Set.Icc (0:ℝ) r, sys.reachSetExact (S := 𝒵) (Set.Icc 0 t) Z U t)
          ((Z.linComb (Z.mtimes (exp (r • toRealMat sys.A)))).plus
            (Zonotope.cube 1 ((Real.exp (r * ‖toRealMat sys.A‖) - 1 - r * ‖toRealMat sys.A‖) * s
              + (Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖
                * μ))).construct := by -- --- PROOF ---
  obtain ⟨hnorm, hgr, hd⟩ := LinearSys.girardExample_spec
  have he : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  refine ⟨LinearSys.canonical (Matrix.diagonal fun _ => 100), ⟨1, fun _ => 1, fun _ _ => 1⟩,
      ⟨0, 0, Fin.elim0⟩,
    0, 1 / 100, 2, ?_, by norm_num, le_rfl, ?_, hgr, ?_⟩
  · show 0 < ‖(Matrix.diagonal fun _ => (100:ℝ) : Mat ℝ 1 1)‖
    rw [hnorm]; norm_num
  · rw [Metric.closedBall_zero]
    ext u
    constructor
    · rintro ⟨β, -, rfl⟩; simp
    · rintro rfl; exact ⟨Fin.elim0, fun j => j.elim0, by simp⟩
  · simp only [Scalar.toRealMat_real, hnorm]
    rw [show (1 / 100 : ℝ) * 100 = 1 by norm_num,
      show (Real.exp 1 - 1 - 1) * 2 + (Real.exp 1 - 1) / 100 * 0 = 2 * (Real.exp 1 - 2) by ring]
    refine lt_of_lt_of_le ?_ hd
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
