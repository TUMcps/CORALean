module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# A cube of a disjunctive normal form

A formula with no `|` above a leaf: a leaf (a comparison, `true`, `false`, `~`, a temporal
operator) or an `&` of leaves. The literals of `getClauses` for a DNF.
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

/-- `φ` is a disjunction of leaves. -/
def STL.Tree.IsCube : STL.Tree n → Prop
  | .or _ _ => False
  | .and φ ψ => IsCube φ ∧ IsCube ψ
  | _ => True

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
