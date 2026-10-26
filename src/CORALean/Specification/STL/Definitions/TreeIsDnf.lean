module

public import CORALean.Specification.STL.Definitions.TreeIsCube

@[expose] public section

/-!
# Disjunctive normal form

A disjunction of cubes (`STL.Tree.IsCube`), the shape `disjunctiveNormalForm.m` returns: no `&`
has an `|` among its operands. Only the `|` and `&` nodes are looked into; a comparison, `~` or a
temporal operator is a leaf, whatever it contains.

## Inputs
* none

## Output
* the formula is a disjunction of cubes
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `φ` is a disjunction of cubes. -/
def STL.Tree.IsDnf : STL.Tree NNReal ℝ n → Prop
  | .or φ ψ => IsDnf φ ∧ IsDnf ψ
  | φ => φ.IsCube

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
