import CORALean.HybridDynamics.Operations.TransitionGuard2Polytope

/-!
# `Transition.guard2polytope` with an exact conversion

An exact conversion (`=`) gives the same guard.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {G P : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)] [∀ n, ContSet (P n) (Vec ℝ n)]
  {L : Type} {𝕋 : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An exact conversion gives the same guard. -/
theorem Transition.guard2polytope_exact (conv : G n → P n)
    (h : ∀ g, construct (conv g) = construct g) (e : Transition G L 𝕋 n) :
    construct (e.guard2polytope conv).guard = construct e.guard :=
  h e.guard

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
