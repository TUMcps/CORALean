module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanPower
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.NthrootFloat
public import CORALean.Specification.SyntaxTree.Operations.SignedRootsFloat

@[expose] public section

/-!
# `aux_power_` over a float scalar

`aux_power_(int,intPrev)` of `syntaxTree.m` for a natural exponent `k`, with the bounds held in `𝕋`:
the `k`-th root of `int` with the sign `intPrev` allows, met with `intPrev`. The roots are bracketed
by `nthrootFloat`, and an even exponent cuts `int` to the nonnegative reals first (`int` certified
below `0` throws `CORA:outOfDomain`). Soundness is `SyntaxTree.funHanPowerFloat_sound`.

## Inputs
* `steps` – bisection steps of the roots
* `k` – exponent
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose power lies in the target
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

/-- `aux_power_`: the `k`-th root of `int` with the sign `intPrev` allows, met with `intPrev`. -/
def SyntaxTree.funHanPowerFloat (steps k : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  if k = 0 then .ok prev
  else if k % 2 = 0 then
    -- even exponent: the argument has to be able to be nonnegative
    if ltStrict (int.sup 0) zero = true then .outOfDomain
    else
      let preInf := (SyntaxTree.nthrootFloat steps (maximum (int.inf 0) zero) k).inf
      let preSup := (SyntaxTree.nthrootFloat steps (int.sup 0) k).sup
      .ok (Float.Interval.intersection prev (SyntaxTree.signedRootsFloat prev preInf preSup))
  else
    let preInf := (SyntaxTree.nthrootFloat steps (int.inf 0) k).inf
    let preSup := (SyntaxTree.nthrootFloat steps (int.sup 0) k).sup
    .ok (Float.Interval.intersection prev ⟨fun _ => preInf, fun _ => preSup⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
