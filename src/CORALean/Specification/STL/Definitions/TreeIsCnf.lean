module

public import CORALean.Specification.STL.Definitions.TreeIsClause

@[expose] public section

/-!
# Conjunctive normal form

A conjunction of clauses (`STL.Tree.IsClause`), the shape `conjunctiveNormalForm.m` returns: no
`|`
has an `&` among its operands. Only the `&` and `|` nodes are looked into; a comparison, `~` or a
temporal operator is a leaf, whatever it contains.
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

/-- `φ` is a conjunction of clauses. -/
def STL.Tree.IsCnf : STL.Tree n → Prop
  | .and φ ψ => IsCnf φ ∧ IsCnf ψ
  | φ => φ.IsClause

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
