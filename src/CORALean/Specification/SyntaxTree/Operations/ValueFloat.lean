module

public import CORALean.Specification.SyntaxTree.Definitions.SyntaxTreeFloat

@[expose] public section

/-!
# `obj.value`: the interval a float node stores

The interval of floats a node of a `Float.SyntaxTree` stores: the root's, whichever the root.

## Inputs
* none

## Output
* the interval the root of the tree stores
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `obj.value`: the interval a node stores. -/
def SyntaxTree.value : SyntaxTree 𝕋 n → SyntaxTree.Dom 𝕋
  | .var _ v => v
  | .unary _ v _ _ => v
  | .binary _ v _ _ _ => v
  | .numLeft _ v _ _ _ => v
  | .numRight _ v _ _ _ => v

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
