import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMatBox

/-!
# How far one order of `inputSolutionFloat` reaches beyond the exact one

Order `i` of the float input solution is `[Tᵢ] U`, the interval `[Tᵢ]` around
the exact `Tᵢ = Aⁱ r^{i+1}/(i+1)!`. This box bounds it from above against `Tᵢ`
applied to `U`'s *nominal* zonotope: `mtimesIntervalMatBox` pays `[Tᵢ] U`'s
excess over `Tᵢ U`, and `[Tᵢ]` applied to `U`'s error box pays what the nominal
zonotope leaves out. A summand of `inputTaylorSumBoxFloat`.
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

/-- What order `i`'s float product `[Tᵢ] U` holds beyond `Tᵢ` applied to `U`'s nominal
zonotope: `[Tᵢ]` on the error box, and the product's own box. -/
def LinearSys.inputTermBoxFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (U : Zonotope (Vec 𝕋 n)) (i : ℕ) :
    Zonotope (Vec 𝕋 n) :=
  let T := MatExp.intervalInputTerm (Interval.point sys.A) r i      -- [Tᵢ]
  Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))  -- [Tᵢ] E
    T U.E.zonotope ⊞
    (Zonotope.mtimesIntervalMatBox T U).zonotope                    -- [Tᵢ] U beyond Tᵢ U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
