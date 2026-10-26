module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanAcosh
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat

@[expose] public section

/-!
# `aaux_cosh_` over a float scalar

`aaux_cosh_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: `cosh` of `int` cut to the
nonnegative reals, met with `intPrev`. The hyperbolic cosine rounds outward (`Interval.cosh`). An
`int` certified below `0` throws `CORA:outOfDomain`. Soundness is
`SyntaxTree.funHanAcoshFloat_sound`.

## Inputs
* `p` – precision of the hyperbolic cosine
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose inverse hyperbolic cosine lies in the target
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

/-- `aaux_cosh_`: `cosh(int)` with `int` cut to `≥ 0`, met with `intPrev`, rounded outward. -/
def SyntaxTree.funHanAcoshFloat (p : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  if ltStrict (int.sup 0) zero = true then .outOfDomain
  else
    -- `int` cut to the nonnegative reals
    let cut : Float.SyntaxTree.Dom 𝕋 := ⟨fun _ => maximum (int.inf 0) zero, fun _ => int.sup 0⟩
    .ok (Float.Interval.intersection prev (Float.Interval.cosh p cut))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
