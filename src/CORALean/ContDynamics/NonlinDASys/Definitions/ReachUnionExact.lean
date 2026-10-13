import CORALean.ContDynamics.NonlinDASys.Definitions.WithSteps

/-!
# Every state, and every algebraic variable, a run reaches within the horizon

`Reach.reachExact` at `NonlinDASys.WithSteps`: every state `x t`, over the trajectories of the
differential-algebraic system itself, on `[0, tFinal]` from a bare initial set under inputs in
`ode.U`, at some time of that horizon. `reachYUnionExact` is the same for the algebraic part
`y t`. Nothing here mentions the reduction: it is how `reach` encloses these sets.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.OfInterval S]
variable {m p n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state a trajectory of `sys.sys` on `[0, tFinal]` from a bare set `X`, under inputs
in `ode.U`, is at within that horizon. -/
def NonlinDASys.WithSteps.reachUnionExact (sys : NonlinDASys.WithSteps S Rg m p n)
    (tFinal : ℝ) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ t ∈ Set.Icc 0 tFinal, {z | ∃ (x : ℝ → Vec ℝ n) (y : ℝ → Vec ℝ p) (u : ℝ → Vec ℝ m),
    sys.sys.Trajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 tFinal) X (construct sys.ode.U)
      x y u ∧ x t = z}

/-- The algebraic variable of such a trajectory, at some time of the horizon. -/
def NonlinDASys.WithSteps.reachYUnionExact (sys : NonlinDASys.WithSteps S Rg m p n)
    (tFinal : ℝ) (X : Set (Vec ℝ n)) : Set (Vec ℝ p) :=
  ⋃ t ∈ Set.Icc 0 tFinal, {z | ∃ (x : ℝ → Vec ℝ n) (y : ℝ → Vec ℝ p) (u : ℝ → Vec ℝ m),
    sys.sys.Trajectory (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 tFinal) X (construct sys.ode.U)
      x y u ∧ y t = z}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
