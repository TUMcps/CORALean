import CORALean.ContDynamics.NonlinearSys.Definitions.ReachParams
import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSet
import CORALean.ContDynamics.NonlinearSys.Definitions.WithSteps

/-!
# Every state a nonlinear run reaches within the horizon

`Reach.reachExact` at `NonlinearSys.WithSteps`: `reachSet` at every time of
`[0, NΔt]`, for runs on that horizon from a bare initial set under inputs in
`U`. The bare set is the representation `Set` itself, which `reachSet` accepts
as it accepts any other. Nothing here mentions the linearizations: they are how
`reach` encloses this set, not part of it.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.OfInterval S]
variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state a run on `[0, p.N * p.Δt]` from a bare initial set `X`, under
inputs in `sys.U`, is at, at some time of that horizon. -/
def NonlinearSys.WithSteps.reachUnionExact (sys : NonlinearSys.WithSteps S Rg m n)
    (p : NonlinearSys.ReachParams) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ t ∈ Set.Icc 0 ((p.N : ℝ) * p.Δt), sys.sys.reachSet (S := fun k => Set (Vec ℝ k))
    (Set.Icc 0 ((p.N : ℝ) * p.Δt)) X (construct sys.U) t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
