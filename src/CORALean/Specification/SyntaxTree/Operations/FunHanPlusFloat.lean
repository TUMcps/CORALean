module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanPlus
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat

@[expose] public section

/-!
# `aux_plus_` over a float scalar

`aux_plus_(int,intPrev1,intPrev2)` of `syntaxTree.m` with the bounds held in `𝕋`: `intPrev1 & (int -
intPrev2)` and `intPrev2 & (int - intPrev1)`. The difference rounds outward (`Interval.minus`).
Soundness is `SyntaxTree.funHanPlusFloat_sound`.

## Inputs
* `int` – target interval
* `prev₁` – first previous interval
* `prev₂` – second previous interval

## Output
* the intervals of the two operands whose sum lies in the target
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_plus_`: `intPrev1 & (int - intPrev2)` and `intPrev2 & (int - intPrev1)`, outward. -/
def SyntaxTree.funHanPlusFloat (int prev₁ prev₂ : Float.SyntaxTree.Dom 𝕋) :
    Float.SyntaxTree.Pair 𝕋 :=
  ⟨Float.Interval.intersection prev₁ (Float.Interval.minus int prev₂),
    Float.Interval.intersection prev₂ (Float.Interval.minus int prev₁)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
