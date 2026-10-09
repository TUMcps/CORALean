import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat

/-!
# A step's end with an input, over a floating-point scalar

`timePointStep`, `e^{Ar} X ⊕ inputSolution`, computed in `𝕋`: the exact
exponential becomes the float interval `[e^{Ar}]` that `expIntervalFloat` takes
at the point range `[r, r]`, and the input solution `inputSolutionFloat`. It is
also the step `discretizeEnclosureFloat`'s `reach` takes with the input
enclosure `inputSolutionFloat` as its input set, before reducing.

`timePointStepFloat` is the same step without an input.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[e^{Ar}] X ⊞ inputSolutionFloat r η U`, at Taylor order `η`. -/
def LinearSys.timePointStepInputFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (X U : Zonotope 𝕋 n) : Zonotope 𝕋 n :=
  let eAr := sys.expIntervalFloat r r η                                     -- [e^{Ar}]
  let P := sys.inputSolutionFloat r η U                                     -- P(r), in floats
  Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) eAr X ⊞ P            -- [e^{Ar}] X ⊞ P

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
