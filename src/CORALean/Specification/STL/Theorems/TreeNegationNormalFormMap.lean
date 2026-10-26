module

public import CORALean.Specification.STL.Operations.TreeMap
public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeNnfWith

@[expose] public section

/-!
# `negationNormalForm` and mapping the times and numbers

The negation normal form pushes `~` to the comparisons and changes only the comparison operators and
the node kinds, so mapping the times and numbers commutes with it.

## Inputs
* `f` – map of the times
* `g` – map of the numbers
* `φ` – formula

## Hypotheses
* none

## Conclusion
* the result of the mapped argument is the mapped result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {τ τ' κ κ' : Type} {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `nnfWith` and mapping the times and numbers. -/
private theorem aux_nnfWith_map (f : τ → τ') (g : κ → κ') (ng : STL.Cmp → STL.Cmp) (b : Bool)
    (φ : STL.Tree τ κ n) :
    (STL.Tree.nnfWith ng b φ).map f g = STL.Tree.nnfWith ng b (φ.map f g) := by
  induction φ generalizing b <;> cases b <;> simp_all [STL.Tree.nnfWith, STL.Tree.map]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.negationNormalForm_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) :
    (φ.negationNormalForm).map f g = (φ.map f g).negationNormalForm :=
  aux_nnfWith_map f g STL.Cmp.negate false φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
