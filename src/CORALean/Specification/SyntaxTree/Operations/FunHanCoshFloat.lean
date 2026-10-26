module

public import CORALean.ContSet.Interval.Float.Operations.Acosh
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanCosh
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.SignedRootsFloat

@[expose] public section

/-!
# `aux_cosh_` over a float scalar

`aux_cosh_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: `acosh` of `int` cut to the
reals from `1`, with the sign `intPrev` allows, met with `intPrev`. The inverse hyperbolic cosine
rounds outward (`Interval.acosh`). An `int` certified below `1` throws `CORA:outOfDomain`. Soundness
is `SyntaxTree.funHanCoshFloat_sound`.

## Inputs
* `p` – precision of the logarithm
* `k` – bisection and root steps
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose hyperbolic cosine lies in the target
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

/-- `aux_cosh_`: `acosh(int)` cut to `≥ 1`, with the sign `intPrev` allows, rounded outward. -/
def SyntaxTree.funHanCoshFloat (p k : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  if ltStrict (int.sup 0) one = true then .outOfDomain
  else
    -- `int` cut to `≥ 1`
    let cut : Float.SyntaxTree.Dom 𝕋 := ⟨fun _ => maximum (int.inf 0) one, fun _ => int.sup 0⟩
    -- apply inverse function
    let res := Float.Interval.acosh p k cut
    .ok (Float.Interval.intersection prev
      (SyntaxTree.signedRootsFloat prev (res.inf 0) (res.sup 0)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
