module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Sin
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsin
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.PiFloat

@[expose] public section

/-!
# `aaux_sin_` over a float scalar

`aaux_sin_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: `sin` of `int`, with `int`
cut to `[-pi/2, pi/2]` below, met with `intPrev`. The sine rounds outward (`Interval.sin`), and
`pi/2` is bounded from above (`piFloat`), so a cut is made only where the bound is certified. An
`int` certified below `-pi/2` throws `CORA:outOfDomain`. Soundness is
`SyntaxTree.funHanAsinFloat_sound`.

## Inputs
* `p` – precision of the sine and of `pi`
* `k` – Newton steps of `pi`
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose inverse sine lies in the target
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

/-- `aaux_sin_`: `sin(int)`, with `int` cut to `[-pi/2, pi/2]` below, met with `intPrev`, rounded
outward. -/
def SyntaxTree.funHanAsinFloat (p k : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  -- `pi/2` from above
  let halfPi := half (SyntaxTree.piFloat p k).sup
  if ltStrict (int.sup 0) (neg halfPi) = true then .outOfDomain
  else
    -- intersection with valid domain
    let cut : Float.SyntaxTree.Dom 𝕋 :=
      if ltStrict (int.inf 0) (neg halfPi) = true then ⟨fun _ => neg halfPi, fun _ => halfPi⟩
      else int
    .ok (Float.Interval.intersection prev (Float.Interval.sin p cut))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
