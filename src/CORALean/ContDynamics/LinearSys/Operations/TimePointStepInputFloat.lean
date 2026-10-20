module

public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat

@[expose] public section

/-!
# A step's end with an input, over a floating-point scalar

`timePointStep`, `e^{Ar} X ⊕ inputSolution`, computed in `𝕋`: the exact
exponential becomes the float interval `[e^{Ar}]` that `expIntervalFloat` takes
at the point range `[r, r]`, and the input solution `inputSolutionFloat`. It is
also the step `discretizeEnclosureFloat`'s `reach` takes with the input
enclosure `inputSolutionFloat` as its input set, before reducing.

`timePointStepFloat` is the same step without an input.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `X` – float state zonotope
* `U` – float input zonotope

## Output
* float zonotope at the end of the step with the input
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[e^{Ar}] X ⊞ inputSolutionFloat r η U`, at Taylor order `η`. -/
def LinearSys.timePointStepInputFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (X U : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let eAr := sys.expIntervalFloat r r η                                     -- [e^{Ar}]
  let P := sys.inputSolutionFloat r η U                                     -- P(r), in floats
  Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- [e^{Ar}] X ⊞ P
    (S := 𝒵[𝕋]) eAr X ⊞ P

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
