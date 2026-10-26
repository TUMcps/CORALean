module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.Tan
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtan
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.PiFloat

@[expose] public section

/-!
# `aaux_tan_` over a float scalar

`aaux_tan_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: `tan` of `int`, cut to
`[-pi/2, pi/2]` below, met with `intPrev`, where `tan(±pi/2) = ±Inf`. The tangent rounds outward
(`tanDown`, `tanUp`) and `pi/2` is bounded on both sides (`piFloat`): a bound of `int` is mapped
only where it is certified strictly inside `(-pi/2, pi/2)` with a positive cosine, and otherwise the
bound of `intPrev` stays. An `int` certified below `-pi/2` throws `CORA:outOfDomain`. Soundness is
`SyntaxTree.funHanAtanFloat_sound`.

## Inputs
* `p` – precision of the tangent and of `pi`
* `k` – Newton steps of `pi`
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose inverse tangent lies in the target
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

/-- `aaux_tan_`: `tan(int)`, with `int` cut to `[-pi/2, pi/2]` below, met with `intPrev`, rounded
outward. -/
def SyntaxTree.funHanAtanFloat (p k : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  -- `pi/2` from below and above
  let halfPiLo := half (SyntaxTree.piFloat p k).inf
  let halfPiHi := half (SyntaxTree.piFloat p k).sup
  if ltStrict (int.sup 0) (neg halfPiHi) = true then .outOfDomain
  else
    -- apply inverse function, `tan(±pi/2) = ±Inf` leaves the bound of `intPrev`
    let preInf := if ltStrict (neg halfPiLo) (int.inf 0) = true ∧
        ltStrict zero (cosDown p (int.inf 0)) = true then tanDown p (int.inf 0) else prev.inf 0
    let preSup := if ltStrict (int.sup 0) halfPiLo = true ∧
        ltStrict zero (cosDown p (int.sup 0)) = true then tanUp p (int.sup 0) else prev.sup 0
    .ok (Float.Interval.intersection prev ⟨fun _ => preInf, fun _ => preSup⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
