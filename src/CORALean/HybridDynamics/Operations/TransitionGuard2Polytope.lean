module

public import CORALean.HybridDynamics.Definitions.Transition

@[expose] public section

/-!
# `Transition.guard2polytope`

CORA's `guard2polytope`: unless the guard is a `levelSet` or a `polytope`, it is replaced by
`polytope(guard)`. A guard's representation is a type parameter here, so the dispatch on the class
is the choice of conversion: `guard2polytope conv` applies `conv`, the representation's own
`polytope` conversion, and leaves the reset and the target as they are. A guard that is a polytope
already needs no call (`conv = id`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {G P : ℕ → Type} {L : Type} {𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The transition with its guard converted by `conv`; reset and target untouched. -/
def Transition.guard2polytope (conv : G n → P n) (e : Transition G L 𝕋 n) :
    Transition P L 𝕋 n :=
  -- `trans.guard = polytope(trans.guard)`
  let guard := conv e.guard
  { guard := guard, W := e.W, w := e.w, target := e.target }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
