import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# The input solution's Taylor orders at every member, in floats

`LinParamSys.inputTaylorSum` computed in `𝕋`: order `i`'s interval matrix
`[Aⁱ r^{i+1}/(i+1)!]` over the whole box `sys.A` is `MatExp.intervalInputTerm`
at `sys.A` itself, times the input set, summed.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⊕_{i ≤ η} [Aⁱ r^{i+1}/(i+1)!] V` over every `A ∈ sys.A`, at index `η`. -/
def LinParamSys.inputTaylorSumFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (r : 𝕋) (V : Zonotope (Vec 𝕋 n)) : ℕ → Zonotope (Vec 𝕋 n)
  | 0 => Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
      (MatExp.intervalInputTerm sys.A r 0) V
  | i + 1 => sys.inputTaylorSumFloat r V i ⊞ Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k))
      (MatExp.intervalInputTerm sys.A r (i + 1)) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
