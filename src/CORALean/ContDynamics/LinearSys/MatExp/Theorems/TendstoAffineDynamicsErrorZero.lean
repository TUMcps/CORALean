module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AffineDynamicsError
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AffineDynamicsErrorNonneg
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsAffineDynamicsErrorLeConstMul

@[expose] public section

/-!
# `Lemma 3`, the limit half: `Δε^h_k(Δt,η) → 0` as `Δt → 0⁺`

[1, Lemma 3]: squeezed between `0` — `err` and `opNorm₂` are both nonnegative — and the linear
bound `exists_affineDynamicsError_le_const_mul` gives eventually, which itself tends to `0`.

The printed proof splits the two summands and reads each at `Δt = 0`; this one keeps them
together, the single bound covering both, since `Δt` divides out of neither.

## Inputs
* `A` – system matrix
* `H` – state zonotope
* `ũ` – constant input
* `η` – Taylor order

## Hypotheses
* none

## Conclusion
* the affine dynamics error tends to zero as the step shrinks

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
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

/-- [1, Lemma 3], the limit half: `Δε^h_k(Δt,η) → 0` as the step shrinks to `0`. -/
theorem MatExp.tendsto_affineDynamicsError_zero (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (η : ℕ) : -- --- CONCL ---
    Tendsto (fun Δt => MatExp.affineDynamicsError A H ũ Δt η)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by -- --- PROOF ---
  obtain ⟨K, hK⟩ := MatExp.exists_affineDynamicsError_le_const_mul A H ũ η
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hKΔt : Tendsto (fun Δt : ℝ => K * Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using hid.const_mul K
  exact squeeze_zero' (Eventually.of_forall fun Δt =>
    MatExp.affineDynamicsError_nonneg A H ũ Δt η) hK hKΔt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
