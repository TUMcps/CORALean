module

public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeToReal
public import CORALean.Specification.STL.Theorems.TreeNegationNormalFormMap

@[expose] public section

/-!
# `negationNormalForm` of a float syntax tree, read as reals

`negationNormalForm` pushes `~` to the comparisons, changing only operators and node kinds, so the
normal form of the tree read as reals is the normal form of the tree, read as reals.

## Inputs
* `φ` – formula

## Hypotheses
* none

## Conclusion
* the result read as reals is the operation on the argument read as reals
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.negationNormalForm_toReal (φ : STL.Tree 𝕋 𝕋 n) :
    φ.negationNormalForm.toReal = φ.toReal.negationNormalForm :=
  STL.Tree.negationNormalForm_map _ _ φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
