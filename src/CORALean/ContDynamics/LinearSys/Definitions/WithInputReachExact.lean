module

public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalReachSetExact
public import CORALean.ContDynamics.LinearSys.Definitions.WithInput

@[expose] public section

/-!
# The exact set `Reach LinearSys.WithInput` is asked to enclose

`timeIntervalReachSetExact` over the horizon `[0, tFinal]`: every state some
`IsCanonicalTrajectory` on that horizon, from a bare initial set and under inputs in
`sys.U`, is at, at some time of it. The bare set is the representation `Set`
itself, which `IsCanonicalTrajectory` accepts as it accepts any other, as
`NonlinearSys.WithSteps.reachUnionExact` does. The windows `reach` covers the
horizon with are how it encloses this set, not part of it.

## Inputs
* `sys` – linear system with input
* `tFinal` – final time
* `𝒳₀` – initial set

## Output
* states a run is in at some time up to the final time
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSetLike

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state a run on `[0, tFinal]` from a bare initial set `𝒳₀`, under inputs
in `sys.U`, is at, at some time of that horizon. -/
def LinearSys.WithInput.reachExact (sys : LinearSys.WithInput 𝕋 S n) (tFinal : ℝ)
    (𝒳₀ : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  sys.sys.timeIntervalReachSetExact (S := 𝒮) (Set.Icc 0 tFinal) 𝒳₀
    (toSet sys.U) tFinal

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
