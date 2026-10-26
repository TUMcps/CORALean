module

public import CORALean.Specification.STL.Operations.ExprMap
public import CORALean.Specification.STL.Definitions.Tree

@[expose] public section

/-!
# Mapping the times and numbers of a syntax tree

The tree with every time bound `a` replaced by `f a` and every number `c` of its comparisons by
`g c`; the shape is kept. At a float scalar `f` and `g` read a stored value as the real it denotes
(`STL.Tree.toReal`).

## Inputs
* `f` – map of the time bounds
* `g` – map of the numbers

## Output
* the tree with the times and numbers mapped
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {τ τ' κ κ' : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The tree with every time bound mapped by `f` and every number by `g`. -/
def STL.Tree.map (f : τ → τ') (g : κ → κ') : STL.Tree τ κ n → STL.Tree τ' κ' n
  | .tt => .tt
  | .ff => .ff
  | .cmp op e₁ e₂ => .cmp op (e₁.map g) (e₂.map g)
  | .not φ => .not (map f g φ)
  | .and φ ψ => .and (map f g φ) (map f g ψ)
  | .or φ ψ => .or (map f g φ) (map f g ψ)
  | .until a b φ ψ => .until (f a) (f b) (map f g φ) (map f g ψ)
  | .release a b φ ψ => .release (f a) (f b) (map f g φ) (map f g ψ)
  | .finally a b φ => .finally (f a) (f b) (map f g φ)
  | .globally a b φ => .globally (f a) (f b) (map f g φ)
  | .next a φ => .next (f a) (map f g φ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
