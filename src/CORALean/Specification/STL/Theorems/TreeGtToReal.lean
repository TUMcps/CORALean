module

public import CORALean.Specification.STL.Operations.Basic
public import CORALean.Specification.STL.Operations.TreeToReal
public import CORALean.Specification.STL.Theorems.TreeCompareMap

@[expose] public section

/-!
# `gt` of float expressions, read as reals

`gt` builds the comparison node, swapping the sides or subtracting them according to which one is a
number and writing the number zero, so the node of two expressions read as reals is the node of the
readings.

## Inputs
* `e₁` – left side
* `e₂` – right side

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

theorem STL.Tree.gt_toReal (e₁ e₂ : STL.Expr 𝕋 n) :
    (STL.Tree.gt e₁ e₂).toReal = STL.Tree.gt e₁.toReal e₂.toReal :=
  STL.Tree.compare_map _ _ toReal_zero .gt e₁ e₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
