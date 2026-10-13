module

public import CORALean.NN.Operations.RefinableNetworkEval

@[expose] public section

/-!
# The exact image a refinement loop encloses

`eval`'s image of an input set: fixed before a level is chosen, so every schedule encloses it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exact image the whole loop is about: fixed before a level is chosen, so
every schedule encloses it. -/
def RefinableNetwork.image (rn : RefinableNetwork S n m) (X : Set (Vec ℝ n)) : Set (Vec ℝ m) :=
  rn.eval '' X

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
