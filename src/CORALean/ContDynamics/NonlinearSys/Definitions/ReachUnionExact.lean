module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSet
public import CORALean.ContDynamics.NonlinearSys.Definitions.WithSteps

@[expose] public section

/-!
# Every state a nonlinear run reaches within the horizon

`Reach.reachExact` at `NonlinearSys.WithSteps`: `reachSet` at every time of
`[0, tFinal]`, for runs on that horizon from a bare initial set under inputs in
`U`. The bare set is the representation `Set` itself, which `reachSet` accepts
as it accepts any other. Nothing here mentions the linearizations or the step:
they are how `reach` encloses this set, not part of it. Positional, as the
mathematics: `Reach` reads the horizon `tFinal - tStart` off `params`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.OfInterval S]
variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state a run on `[0, tFinal]` from a bare initial set `X`, under
inputs in `sys.U`, is at, at some time of that horizon. -/
def NonlinearSys.WithSteps.reachUnionExact (sys : NonlinearSys.WithSteps S Rg m n) (tFinal : ℝ)
    (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ t ∈ Set.Icc 0 tFinal, sys.sys.reachSet (S := 𝒮)
    (Set.Icc 0 tFinal) X (construct sys.U) t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
