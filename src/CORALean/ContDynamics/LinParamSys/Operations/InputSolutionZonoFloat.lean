import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumTailFloat
import CORALean.ContDynamics.LinParamSys.Operations.InputTermZonoFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
import CORALean.ContSet.Conversion.Float.MatZonotope_to_Interval

/-!
# The set every input contributes over one step, at a float matrix zonotope

`LinParamSys.inputSolutionZono` computed in `𝕋` [1, Prop. 3.6]: orders `0` and `1` through
the system's float matrix zonotope (`inputTermZonoFloat`), orders `2 … η` and the remainder
`[E(r)·r]` over the interval matrix it encloses, `sys.A.interval`. The four pieces stay
four products, as printed.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 3.6] in floats: `A_Z r U ⊕ A_Z r²/2! U`, then orders `2 … η` and the remainder
over `A_Z`'s interval matrix. -/
def LinParamSys.inputSolutionZonoFloat (sys : LinParamSys (fun m n => MatZonotope 𝕋 m n) n)
    (r : 𝕋) (η : ℕ) (V : Zonotope 𝕋 n) : Zonotope 𝕋 n :=
  let IA := sys.A.interval                                             -- A_Z's interval matrix
  Mtimes.mtimes (𝕄 := fun m n => MatZonotope 𝕋 m n) (sys.inputTermZonoFloat r 0) V ⊞
    Mtimes.mtimes (𝕄 := fun m n => MatZonotope 𝕋 m n) (sys.inputTermZonoFloat r 1) V ⊞
    (LinParamSys.mk (𝕄 := fun m n => Interval (Mat 𝕋 m n)) IA).inputTaylorSumTailFloat r V η ⊞
    Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (MatExp.intervalInputRemainder IA r η) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
