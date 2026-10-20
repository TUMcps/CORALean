module

public import CORALean.ContDynamics.LinearARX.Operations.Simulate
public import CORALean.ContDynamics.LinearARX.Theorems.StackSimulateZero

@[expose] public section

/-!
# A simulated run is a trajectory

From a start window in `Y₀` and inputs in `U`, the sampled outputs are exactly what
`IsTrajectory` asks of a run: the recursion holds from `p` on by definition, and the first
window is `y₀` read back through the same block indexing.

## Inputs
* `sys` – ARX system
* `Y₀` – initial window set
* `U` – input set
* `y₀` – start window
* `u` – inputs

## Hypotheses
* `hy₀` – start window lies in `Y₀`
* `hu` – inputs lie in `U`

## Conclusion
* the simulated run is a trajectory
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.simulate_isTrajectory (sys : LinearARX 𝕋 dy du p) {Y₀ : S (p * dy)} {U : S du}
    {y₀ : Vec ℝ (p * dy)} (hy₀ : y₀ ∈ construct Y₀) {u : ℕ → Vec ℝ du}
    (hu : ∀ k, u k ∈ construct U) : sys.IsTrajectory Y₀ U (sys.simulate y₀ u) u where
  init := by
    rw [LinearARX.stack_simulate_zero]
    exact hy₀
  input := hu
  step k hk := by
    rw [LinearARX.simulate, dif_neg (not_lt.mpr hk)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
