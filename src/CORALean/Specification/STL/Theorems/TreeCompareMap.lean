module

public import CORALean.Specification.STL.Operations.ExprMap
public import CORALean.Specification.STL.Operations.TreeMap
public import CORALean.Specification.STL.Operations.TreeCompare

@[expose] public section

/-!
# `compare` and mapping the times and numbers

The node of a comparison swaps the sides or subtracts them according to which side is a number, and
the number it writes is zero; a map of the numbers that keeps zero gives the node of the mapped
sides.

## Inputs
* `f` – map of the times
* `g` – map of the numbers
* `op` – comparison
* `e₁` – left side
* `e₂` – right side

## Hypotheses
* `hg` – the map of the numbers keeps zero

## Conclusion
* the mapped node is the node of the mapped sides
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {τ τ' κ κ' : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.compare_map [Zero κ] [Zero κ'] (f : τ → τ') (g : κ → κ') (hg : g 0 = 0)
    (op : STL.Cmp) (e₁ e₂ : STL.Expr κ n) :
    (STL.Tree.compare op e₁ e₂).map f g = STL.Tree.compare op (e₁.map g) (e₂.map g) := by
  cases e₁ <;> cases e₂ <;> simp [STL.Tree.compare, STL.Tree.map, STL.Expr.map, hg]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
