import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.NonlinearSys.Operations.RelinReach

/-!
# Step `i` of the re-linearization loop, over its whole interval

`relinReach` reaches the state at `iΔt` only; this is the set it is in at every
time of step `i`: `LinearSys.timeIntervalStep` of the linearized system at
`(steps i).A`, applied to what `relinReach` reaches at the step's start, plus
step `i`'s own input enclosure — the shape `Trajectory.timeInterval_outer`
proves, not one invented ahead of it.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The enclosure of step `i` of the re-linearization loop over its whole
interval, from what `relinReach` reaches at `iΔt` and step `i`'s input
enclosure. -/
noncomputable def NonlinearSys.relinTimeInterval (sys : NonlinearSys n m) {U : S m} (o : ℕ)
    (ho : 0 < o) (Δt : ℝ) (η : ℕ) (steps : ℕ → sys.LinStep U) (Ud : ℕ → S n) (R₀ : S n) (i : ℕ) :
    S n :=
  ((NonlinearSys.linearize (steps i).A).timeIntervalStep Δt η
    (sys.relinReach o ho Δt steps Ud R₀ i)) ⊞ Ud i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
