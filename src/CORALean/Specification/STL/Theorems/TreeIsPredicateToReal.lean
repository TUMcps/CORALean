module

public import CORALean.Specification.STL.Operations.TreeMap
public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeToReal

@[expose] public section

/-!
# `isPredicate` of a float syntax tree, read as reals

`isPredicate` tests the node kinds only, so a tree is a predicate iff its reading is.

## Inputs
* `φ` – formula

## Hypotheses
* none

## Conclusion
* the reading is a predicate iff the tree is
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {τ τ' κ κ' : Type} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `isPredicate` and mapping the times and numbers. -/
private theorem aux_isPredicate_map (f : τ → τ') (g : κ → κ') (φ : STL.Tree τ κ n) :
    (φ.map f g).isPredicate = φ.isPredicate := by
  induction φ <;> simp_all [STL.Tree.isPredicate, STL.Tree.map]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.isPredicate_toReal (φ : STL.Tree 𝕋 𝕋 n) :
    φ.toReal.isPredicate = φ.isPredicate :=
  aux_isPredicate_map _ _ φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
