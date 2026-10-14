module

public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.Specification.STL.Operations.TreeTemporal

@[expose] public section

/-!
# Numbering the non-temporal sub-formulas

`@stl/assignIdentifiers.m`, `aux_recursive(obj,cnt,list)`: a depth-first, left-to-right walk that
stops at every maximal non-temporal sub-formula, appends it to `list` and gives it the next
identifier, the position in `list` counted from one. The identifier is a field of CORA's object
that `STL.Tree` does not carry, so the result formula is the argument and only `list` is returned;
the counter `cnt` is the length of `list` plus one.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `list` of `aux_recursive(obj,cnt,list)`, started from `list`. -/
def STL.Tree.assignIdentifiersFrom (list : List (STL.Tree n)) : STL.Tree n → List (STL.Tree n)
  | .not φ => if φ.temporal then φ.assignIdentifiersFrom list else list ++ [.not φ]
  | .and φ ψ =>
    if φ.temporal || ψ.temporal then ψ.assignIdentifiersFrom (φ.assignIdentifiersFrom list)
    else list ++ [.and φ ψ]
  | .or φ ψ =>
    if φ.temporal || ψ.temporal then ψ.assignIdentifiersFrom (φ.assignIdentifiersFrom list)
    else list ++ [.or φ ψ]
  | .next _ φ | .finally _ _ φ | .globally _ _ φ => φ.assignIdentifiersFrom list
  | .until _ _ φ ψ | .release _ _ φ ψ => ψ.assignIdentifiersFrom (φ.assignIdentifiersFrom list)
  | φ => list ++ [φ]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
