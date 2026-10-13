import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionTauError
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsParticularSolutionTauErrorLeConstMul

/-!
# `Lemma 4`, the rate half: `Δε^{U,τ}_k(Δt,η) ∼ O(Δt)` as `Δt → 0⁺`

[1, Lemma 4]: `exists_particularSolutionTauError_le_const_mul`'s eventual linear bound is exactly
an `IsBigO` witness once its constant is read at `|K|`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology Asymptotics

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 4], the rate half: `Δε^{U,τ}_k(Δt,η)` is `O(Δt)` as the step shrinks to `0`. -/
theorem MatExp.particularSolutionTauError_isBigO (A : Mat ℝ n n) (tk : ℝ) {U0 : Set (Vec ℝ n)}
    (hU0 : Bornology.IsBounded U0) (η : ℕ) :
    (fun Δt => MatExp.particularSolutionTauError A tk U0 Δt η)
      =O[𝓝[>] (0 : ℝ)] fun Δt : ℝ => Δt := by -- --- PROOF ---
  obtain ⟨K, hK⟩ := MatExp.exists_particularSolutionTauError_le_const_mul A tk hU0 η
  refine IsBigO.of_bound |K| ?_
  filter_upwards [hK, self_mem_nhdsWithin] with Δt hK hΔtmem
  have hΔtpos : (0:ℝ) < Δt := hΔtmem
  have hnn : (0:ℝ) ≤ MatExp.particularSolutionTauError A tk U0 Δt η := err_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_pos hΔtpos]
  exact hK.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hΔtpos.le)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
