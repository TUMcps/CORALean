module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Specification.SyntaxTree.Operations.SignedRoots
public import CORALean.Specification.SyntaxTree.Definitions.SyntaxTreeFloat

@[expose] public section

/-!
# The sign an operand's interval allows, over a float scalar

In `aux_power_` (even exponent) and `aux_cosh_` the two solutions `±r` of `x² = r²` meet the
interval `intPrev` of the operand, with the bounds held in `𝕋`: the positive one if `intPrev` is
certified nonnegative, the negative one if it is certified nonpositive, both otherwise (`[-m, m]`).
`preInf` and `preSup` are bounds of the roots of the two bounds of the target. Soundness is
`SyntaxTree.signedRootsFloat_contains`.

## Inputs
* `prev` – previous interval
* `preInf` – lower root
* `preSup` – upper root

## Output
* the interval of signed roots the previous interval allows
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

/-- The interval of the solutions `±r`, `r` between `preInf` and `preSup`, that `intPrev` allows. -/
def SyntaxTree.signedRootsFloat (prev : Float.SyntaxTree.Dom 𝕋) (preInf preSup : 𝕋) :
    Float.SyntaxTree.Dom 𝕋 :=
  if le zero (prev.inf 0) = true then ⟨fun _ => minimum preInf preSup,
      fun _ => maximum preInf preSup⟩
  else if le (prev.sup 0) zero = true then
    ⟨fun _ => neg (maximum preInf preSup), fun _ => neg (minimum preInf preSup)⟩
  else ⟨fun _ => neg (maximum preInf preSup), fun _ => maximum preInf preSup⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
