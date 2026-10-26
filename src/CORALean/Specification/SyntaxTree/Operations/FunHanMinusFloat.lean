module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanMinus
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat

@[expose] public section

/-!
# `aux_minus_` over a float scalar

`aux_minus_(int,intPrev1,intPrev2)` of `syntaxTree.m` with the bounds held in `𝕋`: `intPrev1 & (int
+ intPrev2)` and `intPrev2 & (intPrev1 - int)`. The sum and the difference round outward
(`Interval.plus`, `Interval.minus`). Soundness is `SyntaxTree.funHanMinusFloat_sound`.

## Inputs
* `int` – target interval
* `prev₁` – first previous interval
* `prev₂` – second previous interval

## Output
* the intervals of the two operands whose difference lies in the target
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

/-- `aux_minus_`: `intPrev1 & (int + intPrev2)` and `intPrev2 & (intPrev1 - int)`, outward. -/
def SyntaxTree.funHanMinusFloat (int prev₁ prev₂ : Float.SyntaxTree.Dom 𝕋) :
    Float.SyntaxTree.Pair 𝕋 :=
  ⟨Float.Interval.intersection prev₁ (Float.Interval.plus int prev₂),
    Float.Interval.intersection prev₂ (Float.Interval.minus prev₁ int)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
