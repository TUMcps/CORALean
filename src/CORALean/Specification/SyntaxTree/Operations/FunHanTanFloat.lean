module

public import CORALean.ContSet.Interval.Float.Operations.Atan
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanTan
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.PeriodicFloat
public import CORALean.Specification.SyntaxTree.Operations.PiFloat

@[expose] public section

/-!
# `aux_tan_` over a float scalar

`aux_tan_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: the branches `atan(int)` and
`atan(int) + pi`, shifted by `2 pi k` (`periodicFloat`). The inverse tangent rounds outward
(`Interval.atan`) and `pi` is bounded on both sides (`piFloat`). Soundness is
`SyntaxTree.funHanTanFloat_sound`.

## Inputs
* `p` – precision of `pi` and of the inverse tangent
* `k` – Newton steps
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose tangent lies in the target
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

/-- `aux_tan_`: the branches `atan(int)` and `atan(int) + pi` shifted by `2 pi k`, outward. -/
def SyntaxTree.funHanTanFloat (p k : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  -- apply inverse function
  let resTemp₁ := Float.Interval.atan p k int
  let piI := SyntaxTree.piFloat (𝕋 := 𝕋) p k
  let resTemp₂ : Float.SyntaxTree.Dom 𝕋 :=
    ⟨fun _ => addDown (resTemp₁.inf 0) piI.inf, fun _ => addUp (resTemp₁.sup 0) piI.sup⟩
  .ok (SyntaxTree.periodicFloat p k resTemp₁ resTemp₂ prev)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
