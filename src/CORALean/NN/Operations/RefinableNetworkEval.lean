import CORALean.NN.Definitions.RefinableNetwork

/-!
# What a refinable network computes

Defined on the network and not read off a schedule, which is the point of `RefinableLayer`
keeping `eval` outside `enclose`: the exact image is one set, fixed before any level is chosen,
and every schedule encloses that same set.
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

def RefinableNetwork.eval : ∀ {n m : ℕ}, RefinableNetwork S n m → Vec ℝ n → Vec ℝ m
  | _, _, .nil, x => x
  | _, _, .cons L rest, x => rest.eval (L.eval x)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
