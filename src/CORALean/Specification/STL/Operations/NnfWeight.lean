module

public import CORALean.Specification.STL.Definitions.Nnf

@[expose] public section

/-!
# The weight of a normal form

A measure for [1, Lemma 4]'s rewriting: it falls from `φ U[i,j] ψ` to `φ`, `ψ` and `φ U[i-1,j-1]
ψ`, which is why the iteration ends.

## Inputs
* none

## Output
* the weight of the normal form

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The weight; an `U[i,j]` or `R[i,j]` weighs `j + 1` times its operands. -/
def STL.Nnf.weight : STL.Nnf X → ℕ
  | .lit _ => 1
  | .and φ ψ => φ.weight + ψ.weight + 1
  | .or φ ψ => φ.weight + ψ.weight + 1
  | .until _ j φ ψ => (j + 1) * (φ.weight + ψ.weight + 1)
  | .release _ j φ ψ => (j + 1) * (φ.weight + ψ.weight + 1)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
