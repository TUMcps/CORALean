module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# The branches of a tree of reach sets

The tree is given by `children`, the indices of the children of a node (`children(R,i)`); the root
is `0` and has no entry. `IsBranch children i w` says that `w` is the list of the entries analyzed
on the way from `i` (included, unless it is the root) down to a leaf, one child after the other.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- `w` lists the entries analyzed on a way from node `i` down to a leaf of the tree given by
`children`. -/
inductive ReachSetAnalyzer.IsBranch (children : ℕ → List ℕ) : ℕ → List ℕ → Prop
  | leaf (i : ℕ) : children i = [] → IsBranch children i (if i ≠ 0 then [i] else [])
  | node (i j : ℕ) (w : List ℕ) : j ∈ children i → IsBranch children j w →
      IsBranch children i ((if i ≠ 0 then [i] else []) ++ w)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
