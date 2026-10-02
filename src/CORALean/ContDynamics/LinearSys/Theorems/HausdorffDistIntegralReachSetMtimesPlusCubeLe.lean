import CORALean.ContDynamics.LinearSys.Theorems.IntegralReachSetSubsetMtimesPlusCube
import CORALean.ContDynamics.LinearSys.Theorems.ExistsMemInputReachDistLe

/-!
# One step of the flow: the enclosure converges

[1, Lemma 1], second half: `d_H(Φ_r(Z), e^{rA}Z + □(β_r)) ≤ µ‖A‖e^{r‖A‖}r²`, the Hausdorff
distance in [1]'s infinity norm, which is `Vec ℝ n`'s own. One direction is the first half,
`integralReachSet_subset_mtimes_plus_cube`; the other is
`exists_mem_inputReach_dist_le`: a point `e^{rA}z + w` of the enclosure is within the
bound of `e^{rA}z + v`, `v` what a constant input reaches.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1], convergence: `d_H(Φ_r(Z), e^{rA}Z + □(β_r)) ≤ µ‖A‖e^{r‖A‖}r²`. -/
theorem LinearSys.hausdorffDist_integralReachSet_mtimes_plus_cube_le (sys : LinearSys 𝕋 n)
    (Z U : Zonotope (Vec ℝ n)) {μ r : ℝ} (hA : 0 < ‖toRealMat sys.A‖) (hr : 0 ≤ r)
    (hμ : 0 ≤ μ) (hU : U.construct = Metric.closedBall 0 μ) :
    Metric.hausdorffDist (sys.integralReachSet (S := 𝒵) (Set.Icc 0 r) Z U r)
      ((Z.mtimes (exp (r • toRealMat sys.A))).plus
          (Zonotope.cube n ((Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖
            * μ))).construct
      ≤ μ * ‖toRealMat sys.A‖ * Real.exp (r * ‖toRealMat sys.A‖)
        * r ^ 2 := by -- --- PROOF ---
  have hx := Real.add_one_le_exp (r * ‖toRealMat sys.A‖)
  have hx0 := mul_nonneg hr hA.le
  have hβ : 0 ≤ (Real.exp (r * ‖toRealMat sys.A‖) - 1) / ‖toRealMat sys.A‖ * μ :=
    mul_nonneg (div_nonneg (by linarith) hA.le) hμ
  have hbound : 0 ≤ μ * ‖toRealMat sys.A‖ * Real.exp (r * ‖toRealMat sys.A‖) * r ^ 2 := by
    have := Real.exp_nonneg (r * ‖toRealMat sys.A‖)
    positivity
  refine Metric.hausdorffDist_le_of_mem_dist hbound
    (fun y hy => ⟨y, sys.integralReachSet_subset_mtimes_plus_cube Z U hA hr hμ hU hy,
      by rw [dist_self]; exact hbound⟩) ?_
  -- a point `e^{rA}z + w` of the enclosure, against what a constant input reaches
  intro q hq
  rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact, Zonotope.cube_exact n hβ] at hq
  obtain ⟨_, ⟨z, hz, rfl⟩, w, hw, rfl⟩ := hq
  obtain ⟨v, hv, hdist⟩ := sys.exists_mem_inputReach_dist_le hA hr hμ (S := 𝒵) (U := U)
    (by rw [show construct U = U.construct from rfl, hU]) (mem_closedBall_zero_iff.mp hw)
  refine ⟨exp (r • toRealMat sys.A) *ᵥ z + v, ?_, ?_⟩
  · rw [sys.integralReachSet_eq (S := 𝒵) Z U hr (Zonotope.isBounded_construct U)]
    exact ⟨_, ⟨z, hz, rfl⟩, v, hv, rfl⟩
  · rwa [dist_add_left]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
