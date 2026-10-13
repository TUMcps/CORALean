module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionTauError
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsParticularSolutionTauErrorLeConstMul

@[expose] public section

/-!
# `Lemma 4`, the limit half: `Δε^{U,τ}_k(Δt,η) → 0` as `Δt → 0⁺`

[1, Lemma 4]: squeezed between `0` (`err` is always nonnegative) and the linear bound
`exists_particularSolutionTauError_le_const_mul` gives eventually, which itself tends to `0`.

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

/-- [1, Lemma 4], the limit half: `Δε^{U,τ}_k(Δt,η) → 0` as the step shrinks to `0`. -/
theorem MatExp.tendsto_particularSolutionTauError_zero (A : Mat ℝ n n) (tk : ℝ)
    {U0 : Set (Vec ℝ n)} (hU0 : Bornology.IsBounded U0) (η : ℕ) :
    Tendsto (fun Δt => MatExp.particularSolutionTauError A tk U0 Δt η)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by -- --- PROOF ---
  obtain ⟨K, hK⟩ := MatExp.exists_particularSolutionTauError_le_const_mul A tk hU0 η
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hKΔt : Tendsto (fun Δt : ℝ => K * Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using hid.const_mul K
  exact squeeze_zero' (Eventually.of_forall fun _ => err_nonneg _) hK hKΔt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
