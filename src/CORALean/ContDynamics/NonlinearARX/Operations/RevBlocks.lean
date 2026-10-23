module

public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# The newest-first order of a stacked history

An index of the `p * d` stacked entries of a window is a block of `d` entries and a position in it.
The block order is reversed, so the oldest block is read last, as the conversion to a discrete-time
system of [1] reads the window and the inputs newest first. The position inside the block stays.

## Inputs
* `s` – index of a stacked entry

## Output
* index of the entry in the block-reversed order

## References

* [1] `contDynamics/@nonlinearARX/nonlinearSysDT.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {p d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The index with its block reversed and its position in the block kept. -/
abbrev NonlinearARX.revBlocks (s : Fin (p * d)) : Fin (p * d) :=
  finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1, (finProdFinEquiv.symm s).2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
