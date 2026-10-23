module

public import CORALean.Global.Tensor

@[expose] public section

/-!
# Every index passing its check

A conjunction over `Fin k`, as a fold rather than a `Finset`: the recursion is what proofs see,
and `@[csimp]` swaps in the same conjunction as a loop, giving up the early exit on the first
`false`, which only a check that fails would have reached.

## Inputs
* none

## Output
* true iff every index passes its check
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every index passing its own check, as a fold rather than a `Finset`. -/
def allOver : {k : ℕ} → (Fin k → Bool) → Bool
  | 0, _ => true
  | _ + 1, f => f 0 && allOver fun i => f i.succ


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The same conjunction as a loop. -/
def aux_allOverImpl {k : ℕ} (f : Fin k → Bool) : Bool :=
  Fin.foldr k (fun i acc => f i && acc) true

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
