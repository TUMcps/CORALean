import CORALean.ContDynamics.LinearSys.Theorems.FlowIci

/-!
# The input as a derivative, drift subtracted

`u` as a derivative minus the drift. The flow states the sum; this is the
rearrangement that leaves `u` alone on one side, which is what carries
measurability to `u` itself rather than to the integrand. Needed by both
`aestronglyMeasurable_input` and `aestronglyMeasurable_input_reflected`, so it
is stated once here rather than duplicated into each.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.input_eq_derivWithin {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory T R₀ U x u) {a b t : ℝ}
    (hT : Set.Icc a b ⊆ T) (ht : t ∈ Set.Ico a b) :
    u t = derivWithin x (Set.Ici t) t - toRealMat sys.A *ᵥ x t := by
  rw [(traj.flow_Ici hT ht).derivWithin (uniqueDiffWithinAt_Ici t)]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
