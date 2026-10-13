import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionError
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsParticularSolutionErrorLeConstMulSq

/-!
# `Lemma 2`, the limit half: `Δε^U_k(Δt,η) → 0` as `Δt → 0⁺`

[1, Lemma 2]: squeezed between `0` (`err` is always nonnegative) and the quadratic bound
`exists_particularSolutionError_le_const_mul_sq` gives eventually, which itself tends to `0`.

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

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2], the limit half: `Δε^U_k(Δt,η) → 0` as the step shrinks to `0`. -/
theorem MatExp.tendsto_particularSolutionError_zero (A : Mat ℝ n n) (tk : ℝ)
    {U0 : Set (Vec ℝ n)} (hU0 : Bornology.IsBounded U0) (η : ℕ) :
    Tendsto (fun Δt => MatExp.particularSolutionError A tk U0 Δt η)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by -- --- PROOF ---
  obtain ⟨K, hK⟩ := MatExp.exists_particularSolutionError_le_const_mul_sq A tk hU0 η
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun Δt : ℝ => Δt ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.pow 2
  have hKΔt : Tendsto (fun Δt : ℝ => K * Δt ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hsq.const_mul K
  have hnn : ∀ Δt, (0:ℝ) ≤ MatExp.particularSolutionError A tk U0 Δt η := fun Δt =>
    add_nonneg (err_nonneg _) (err_nonneg _)
  exact squeeze_zero' (Eventually.of_forall hnn) hK hKΔt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
