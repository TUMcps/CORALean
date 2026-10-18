module

public import CORALean.ContDynamics.LinearSys.Theorems.IUnionReachSetSubsetLinCombPlusCube
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsMemIUnionReachSetDistLe

@[expose] public section

/-!
# The first time interval: the enclosure converges

[1, Lemma 2], second half, corrected:
`d_H(R_[0,r](Z), P + □(α_r + β_r)) ≤ r‖A‖e^{r‖A‖}(µ/‖A‖ + (1/2 + r‖A‖) sup ‖x‖)`. One
direction is the first half, `iUnion_reachSet_subset_linComb_plus_cube`; the other is
`exists_mem_iUnion_reachSet_dist_le`.

[1] prints `(1/2 + r)` where this has `(1/2 + r‖A‖)`. The printed proof reaches its factor
through `2α_r ≤ e^{r‖A‖} r² sup ‖x‖`, which drops `‖A‖²`, and the printed bound is false:
`exists_lt_hausdorffDist_iUnion_reachSet` is a scalar system where the distance
exceeds it. With `r‖A‖` in place of `r` the bound is dimensionally consistent, `r‖A‖` being
unitless where `r` is a time.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
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

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2], convergence, with `(1/2 + r‖A‖)` for the printed `(1/2 + r)`:
`d_H(R_[0,r](Z), P + □(α_r + β_r)) ≤ r‖A‖e^{r‖A‖}(µ/‖A‖ + (1/2 + r‖A‖) sup ‖x‖)`. -/
theorem LinearSys.hausdorffDist_iUnion_reachSet_linComb_plus_cube_le
    (sys : LinearSys 𝕋 n) (Z U : Zonotope (Vec ℝ n)) {μ r s : ℝ} (hA : 0 < ‖toRealMat sys.A‖)
    (hr : 0 < r) (hμ : 0 ≤ μ) (hU : U.construct = Metric.closedBall 0 μ)
    (hs : ∀ z ∈ Z.construct, ‖z‖ ≤ s) : -- --- STMT ---
    Metric.hausdorffDist
      (⋃ t ∈ Set.Icc (0:ℝ) r, sys.reachSet (S := 𝒵) (Set.Icc 0 t) Z U t)
      ((Z.linComb (Z.mtimes (exp (r • toRealMat sys.A)))).plus
          (Zonotope.cube n ((Real.exp (r * ‖toRealMat sys.A‖) - 1 - r * ‖toRealMat sys.A‖) * s
            + (Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖ * μ))).construct
      ≤ r * ‖toRealMat sys.A‖ * Real.exp (r * ‖toRealMat sys.A‖)
        * (μ / ‖toRealMat sys.A‖ + (1 / 2 + r * ‖toRealMat sys.A‖) * s) := by -- --- PROOF ---
  have hs0 : 0 ≤ s := (norm_nonneg Z.c).trans (hs _ (Zonotope.center_mem_construct Z))
  have hbound : 0 ≤ r * ‖toRealMat sys.A‖ * Real.exp (r * ‖toRealMat sys.A‖)
      * (μ / ‖toRealMat sys.A‖ + (1 / 2 + r * ‖toRealMat sys.A‖) * s) := by
    have := Real.exp_nonneg (r * ‖toRealMat sys.A‖)
    have := div_nonneg hμ hA.le
    have := mul_nonneg hr.le hA.le
    positivity
  refine Metric.hausdorffDist_le_of_mem_dist hbound
    (fun y hy => ⟨y, sys.iUnion_reachSet_subset_linComb_plus_cube Z U hA hr.le hμ hU hs hy,
      by rw [dist_self]; exact hbound⟩)
    (fun q hq => sys.exists_mem_iUnion_reachSet_dist_le Z U hA hr hμ hU hs hq)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
