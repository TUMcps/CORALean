module

public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalReachSet
public import CORALean.ContDynamics.LinearSys.Definitions.WithInput

@[expose] public section

/-!
# The exact set `Reach LinearSys.WithInput` is asked to enclose

`timeIntervalReachSet` over the horizon `[0, tFinal]`: every state some
`Trajectory` on that horizon, from a bare initial set and under inputs in
`sys.U`, is at, at some time of it. The bare set is the representation `Set`
itself, which `Trajectory` accepts as it accepts any other, as
`NonlinearSys.WithSteps.reachUnionExact` does. The windows `reach` covers the
horizon with are how it encloses this set, not part of it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state a run on `[0, tFinal]` from a bare initial set `X`, under inputs
in `sys.U`, is at, at some time of that horizon. -/
def LinearSys.WithInput.reachExact (sys : LinearSys.WithInput 𝕋 S n) (tFinal : ℝ)
    (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  sys.sys.timeIntervalReachSet (S := 𝒮) (Set.Icc 0 tFinal) X
    (construct sys.U) tFinal

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
