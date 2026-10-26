module

public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# A property of every time bound of a syntax tree

Every time bound of the tree has the property `P`. For a float tree, `P` is that the bound denotes
a nonnegative real, which CORA's `stlInterval` guarantees.

## Inputs
* `P` – property of a time bound

## Output
* whether every time bound of the tree has it
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {τ κ : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every time bound of the tree satisfies `P`. -/
def STL.Tree.HasAllTimes (P : τ → Prop) : STL.Tree τ κ n → Prop
  | .tt => True
  | .ff => True
  | .cmp _ _ _ => True
  | .not φ => φ.HasAllTimes P
  | .and φ ψ => φ.HasAllTimes P ∧ ψ.HasAllTimes P
  | .or φ ψ => φ.HasAllTimes P ∧ ψ.HasAllTimes P
  | .until a b φ ψ => P a ∧ P b ∧ φ.HasAllTimes P ∧ ψ.HasAllTimes P
  | .release a b φ ψ => P a ∧ P b ∧ φ.HasAllTimes P ∧ ψ.HasAllTimes P
  | .finally a b φ => P a ∧ P b ∧ φ.HasAllTimes P
  | .globally a b φ => P a ∧ P b ∧ φ.HasAllTimes P
  | .next a φ => P a ∧ φ.HasAllTimes P

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
