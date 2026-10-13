import CORALean.HybridDynamics.Operations.TransitionGuard2Polytope

/-!
# `Transition.guard2polytope` keeps the reset

The reset is untouched, so it is the same map.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {G P : ℕ → Type} {L : Type} {𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reset is untouched, so it is the same map. -/
theorem Transition.guard2polytope_reset (conv : G n → P n) (e : Transition G L 𝕋 n) :
    (e.guard2polytope conv).reset = e.reset := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
