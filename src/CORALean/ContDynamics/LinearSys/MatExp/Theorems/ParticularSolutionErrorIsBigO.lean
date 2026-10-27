module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionError
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsParticularSolutionErrorLeConstMulSq

@[expose] public section

/-!
# `Lemma 2`, the rate half: `Δε^U_k(Δt,η) ∼ O(Δt²)` as `Δt → 0⁺`

[1, Lemma 2]: `exists_particularSolutionError_le_const_mul_sq`'s eventual quadratic bound is
exactly an `IsBigO` witness once its constant is read at `|K|`.

## Inputs
* `A` – system matrix
* `tk` – step start time
* `U0` – input set
* `η` – Taylor order

## Hypotheses
* `hU0` – input set bounded

## Conclusion
* the error is of the order of the squared step as the step shrinks to zero

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
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

/-- [1, Lemma 2], the rate half: `Δε^U_k(Δt,η)` is `O(Δt²)` as the step shrinks to `0`. -/
theorem MatExp.particularSolutionError_isBigO (A : Mat ℝ n n) (tk : ℝ) {U0 : Set (Vec ℝ n)}
    (hU0 : Bornology.IsBounded U0) (η : ℕ) : -- --- CONCL ---
    (fun Δt => MatExp.particularSolutionError A tk U0 Δt η)
      =O[𝓝[>] (0 : ℝ)] fun Δt : ℝ => Δt ^ 2 := by -- --- PROOF ---
  obtain ⟨K, hK⟩ := MatExp.exists_particularSolutionError_le_const_mul_sq A tk hU0 η
  refine IsBigO.of_bound |K| ?_
  filter_upwards [hK, self_mem_nhdsWithin] with Δt hK hΔtmem
  have hΔtpos : (0:ℝ) < Δt := hΔtmem
  have hnn : (0:ℝ) ≤ MatExp.particularSolutionError A tk U0 Δt η :=
    add_nonneg (err_nonneg _) (err_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg (sq_nonneg Δt)]
  exact hK.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg Δt))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
