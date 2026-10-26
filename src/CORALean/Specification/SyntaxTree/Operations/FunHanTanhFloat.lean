module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.Atanh
public import CORALean.Specification.SyntaxTree.Operations.FunHanTanh
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat

@[expose] public section

/-!
# `aux_tanh_` over a float scalar

`aux_tanh_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: `atanh` of `int` cut to
`[-1,1]`, met with `intPrev`, where `atanh(±1) = ±Inf`. The inverse hyperbolic tangent rounds
outward (`atanhDown`, `atanhUp`): a bound of the cut `int` is mapped only where it is certified
strictly inside `(-1,1)`, and otherwise the bound of `intPrev` stays. Soundness is
`SyntaxTree.funHanTanhFloat_sound`.

## Inputs
* `p` – precision of the logarithm
* `k` – bisection steps of the logarithm
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose hyperbolic tangent lies in the target
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

/-- `aux_tanh_`: `atanh(int & interval(-1,1))` met with `intPrev`, rounded outward. -/
def SyntaxTree.funHanTanhFloat (p k : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  -- intersection with valid domain
  let lo := maximum (int.inf 0) (neg one)
  let hi := minimum (int.sup 0) one
  -- apply inverse function, `atanh(±1) = ±Inf` leaves the bound of `intPrev`
  let preInf := if ltStrict zero (subDown one (neg lo)) = true then atanhDown p k lo
    else prev.inf 0
  let preSup := if ltStrict zero (subDown one hi) = true then atanhUp p k hi else prev.sup 0
  .ok (Float.Interval.intersection prev ⟨fun _ => preInf, fun _ => preSup⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
