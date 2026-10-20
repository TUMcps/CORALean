module

public import CORALean.Global.DmdStack

@[expose] public section

/-!
# The blocks of a stacked matrix are the blocks

`dmdBlocks (dmdStack A B c) = (A, B, c)`.
The source is [1].

## Inputs
* `A` – state matrix
* `B` – input matrix
* `c` – offset vector

## Hypotheses
* none

## Conclusion
* the blocks of the stacked matrix are the original blocks

## References

* [1] `contDynamics/@linearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem dmdBlocks_dmdStack (A : Mat ℝ n n) (B : Mat ℝ n m) (c : Vec ℝ n) :
    dmdBlocks (dmdStack A B c) = (A, B, c) := by
  simp [dmdBlocks, dmdStack, Fin.append_left, Fin.append_right, Fin.snoc_castSucc,
    Fin.snoc_last]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
