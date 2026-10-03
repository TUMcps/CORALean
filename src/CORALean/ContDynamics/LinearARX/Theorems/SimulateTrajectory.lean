import CORALean.ContDynamics.LinearARX.Operations.Simulate
import CORALean.ContDynamics.LinearARX.Theorems.StackSimulateZero

/-!
# A simulated run is a trajectory

From a start window in `Y₀` and inputs in `U`, the sampled outputs are exactly what
`Trajectory` asks of a run: the recursion holds from `p` on by definition, and the first
window is `y₀` read back through the same block indexing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.simulate_trajectory (sys : LinearARX 𝕋 dy du p) {Y₀ : S (p * dy)} {U : S du}
    {y₀ : Vec ℝ (p * dy)} (hy₀ : y₀ ∈ construct Y₀) {u : ℕ → Vec ℝ du}
    (hu : ∀ k, u k ∈ construct U) : sys.Trajectory Y₀ U (sys.simulate y₀ u) u where
  init := by
    rw [LinearARX.stack_simulate_zero]
    exact hy₀
  input := hu
  step k hk := by
    rw [LinearARX.simulate, dif_neg (not_lt.mpr hk)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
