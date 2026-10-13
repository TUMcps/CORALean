module

public import CORALean.NN.Definitions.Chain

@[expose] public section

/-!
# A chain's composite

The function a network is sound at: every layer's map, applied left to right as the layers are.
Structural recursion over the chain, so it is data and not a proposition, but nothing runs it:
every map it composes is a real function.
-/

-- Authors:       Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The composite, applied left to right as the layers are. -/
def Chain.eval : ∀ {n m : ℕ}, Chain n m → Vec ℝ n → Vec ℝ m
  | _, _, .nil, x => x
  | _, _, .cons f rest, x => rest.eval (f x)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
