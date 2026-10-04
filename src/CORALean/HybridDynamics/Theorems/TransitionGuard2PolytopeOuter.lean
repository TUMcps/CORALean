import CORALean.HybridDynamics.Operations.TransitionGuard2Polytope

/-!
# `Transition.guard2polytope` with an outer conversion

An outer conversion (`⊆`) gives a guard that contains the old one, so every jump of the old
transition is a jump of the new one.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {G P : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] [∀ n, ContSet (P n) (Vec ℝ n)]
  {L : Type} {𝕋 : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An outer conversion gives an outer guard: the old guard lies inside the new one. -/
theorem Transition.guard2polytope_outer (conv : G n → P n)
    (h : ∀ g, construct g ⊆ construct (conv g)) (e : Transition G L 𝕋 n) :
    construct e.guard ⊆ construct (e.guard2polytope conv).guard :=
  h e.guard

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
