module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanTimes
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat

@[expose] public section

/-!
# `aux_times_` over a float scalar

`aux_times_(int,intPrev1,intPrev2)` of `syntaxTree.m` with the bounds held in `𝕋`: `intPrev1 & (int
/ intPrev2)` where `0` is certified outside `intPrev2`, and the same for `intPrev2`; an operand
whose partner may contain `0` keeps its interval. The quotient rounds outward (`Interval.rdivide`).
Soundness is `SyntaxTree.funHanTimesFloat_sound`.

## Inputs
* `int` – target interval
* `prev₁` – first previous interval
* `prev₂` – second previous interval

## Output
* the intervals of the two operands whose product lies in the target
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

/-- `aux_times_`: `intPrev1 & (int / intPrev2)` where `0 ∉ intPrev2`, and the same for `intPrev2`,
rounded outward. -/
def SyntaxTree.funHanTimesFloat (int prev₁ prev₂ : Float.SyntaxTree.Dom 𝕋) :
    Float.SyntaxTree.Pair 𝕋 :=
  let res₁ := if ltStrict zero (prev₂.inf 0) = true ∨ ltStrict (prev₂.sup 0) zero = true then
    Float.Interval.intersection prev₁ (Float.Interval.rdivide int prev₂) else prev₁
  let res₂ := if ltStrict zero (prev₁.inf 0) = true ∨ ltStrict (prev₁.sup 0) zero = true then
    Float.Interval.intersection prev₂ (Float.Interval.rdivide int prev₁) else prev₂
  ⟨res₁, res₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
