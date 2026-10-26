module

public import CORALean.ContSet.Interval.Float.Operations.Acos
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanCos
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.PeriodicFloat
public import CORALean.Specification.SyntaxTree.Operations.PiFloat

@[expose] public section

/-!
# `aux_cos_` over a float scalar

`aux_cos_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: the branches `acos(int)` and
`-acos(int)`, shifted by `2 pi k` (`periodicFloat`). The inverse cosine rounds outward
(`Interval.acos`). Soundness is `SyntaxTree.funHanCosFloat_sound`.

## Inputs
* `p` – precision of `pi` and of the inverse cosine
* `k` – Newton steps
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose cosine lies in the target
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

/-- `aux_cos_`: the branches `acos(int)` and `-acos(int)` shifted by `2 pi k`, rounded outward. -/
def SyntaxTree.funHanCosFloat (p k : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  -- intersection with valid domain
  let cut := Float.Interval.intersection int (SyntaxTree.intervalFloat (neg one) one)
  -- apply inverse function
  let resTemp₁ := Float.Interval.acos p k cut
  let resTemp₂ : Float.SyntaxTree.Dom 𝕋 :=
    ⟨fun _ => neg (resTemp₁.sup 0), fun _ => neg (resTemp₁.inf 0)⟩
  .ok (SyntaxTree.periodicFloat p k resTemp₁ resTemp₂ prev)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
