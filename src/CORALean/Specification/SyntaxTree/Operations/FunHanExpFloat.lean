module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.Log
public import CORALean.Specification.SyntaxTree.Operations.FunHanExp
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat

@[expose] public section

/-!
# `aux_exp_` over a float scalar

`aux_exp_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: the logarithm of `int` cut to
the positive reals, met with `intPrev`. The lower bound rounds down (`logDown`, from `1` on) and the
upper one up (`logUp`, from `0` on); where the cut bound is not certified in that range (`log(0) =
-Inf` among them) the bound of `intPrev` stays. An `int` certified below `0` throws
`CORA:outOfDomain`. Soundness is `SyntaxTree.funHanExpFloat_sound`.

## Inputs
* `p` – precision of the exponentials
* `k` – bisection steps of the logarithms
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose exponential lies in the target
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

/-- `aux_exp_`: `log(int)` cut to the positive reals, met with `intPrev`, rounded outward. -/
def SyntaxTree.funHanExpFloat (p k : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  -- `int` cut to the positive reals
  let lo := maximum (int.inf 0) zero
  if ltStrict (int.sup 0) zero = true then .outOfDomain
  else
    -- `log(int)`, the bound of `intPrev` where the logarithm is not certified
    let pre : Float.SyntaxTree.Dom 𝕋 :=
      ⟨fun _ => if le one lo = true then logDown p k lo else prev.inf 0,
        fun _ => if ltStrict zero (int.sup 0) = true then logUp p k (int.sup 0) else prev.sup 0⟩
    .ok (Float.Interval.intersection prev pre)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
