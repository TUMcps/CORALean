module

public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalReachSet
public import CORALean.ContDynamics.LinearSys.Definitions.WithInputSplit

@[expose] public section

/-!
# The exact set `Reach LinearSys.WithInputSplit` is asked to enclose

`LinearSys.WithInput.reachExact`'s set, with the input set anywhere:
`timeIntervalReachSet` over the horizon `[0, tFinal]`, every state some
`IsTrajectory` on it, from a bare initial set and under inputs in `sys.U`, is at,
at some time of it. The split of `U` and the windows are how `reach` encloses
this set, not part of it.
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
def LinearSys.WithInputSplit.reachExact (sys : LinearSys.WithInputSplit 𝕋 S n) (tFinal : ℝ)
    (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  sys.sys.timeIntervalReachSet (S := 𝒮) (Set.Icc 0 tFinal) X
    (construct sys.U) tFinal

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
