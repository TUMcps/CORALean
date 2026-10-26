module

public import CORALean.ContSet.Interval.Float.Operations.Asin
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanSin
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.PeriodicFloat
public import CORALean.Specification.SyntaxTree.Operations.PiFloat

@[expose] public section

/-!
# `aux_sin_` over a float scalar

`aux_sin_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: the branches `asin(int)` and
`pi - asin(int)`, shifted by `2 pi k` (`periodicFloat`). The inverse sine rounds outward
(`Interval.asin`) and `pi` is bounded on both sides (`piFloat`). Soundness is
`SyntaxTree.funHanSinFloat_sound`.

## Inputs
* `p` – precision of `pi` and of the inverse sine
* `k` – Newton steps
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose sine lies in the target
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_sin_`: the branches `asin(int)` and `pi - asin(int)` shifted by `2 pi k`, outward. -/
def SyntaxTree.funHanSinFloat (p k : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  -- intersection with valid domain
  let cut := Float.Interval.intersection int (SyntaxTree.intervalFloat (neg one) one)
  -- apply inverse function
  let resTemp₁ := Float.Interval.asin p k cut
  let piI := SyntaxTree.piFloat (𝕋 := 𝕋) p k
  let resTemp₂ : Float.SyntaxTree.Dom 𝕋 :=
    ⟨fun _ => subDown piI.inf (resTemp₁.sup 0), fun _ => subUp piI.sup (resTemp₁.inf 0)⟩
  .ok (SyntaxTree.periodicFloat p k resTemp₁ resTemp₂ prev)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
