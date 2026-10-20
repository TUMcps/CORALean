module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# The input solution's Taylor orders at every member, in floats

`LinParamSys.inputTaylorSum` computed in `𝕋`: order `i`'s interval matrix
`[Aⁱ r^{i+1}/(i+1)!]` over the whole box `sys.A` is `MatExp.intervalInputTerm`
at `sys.A` itself, times the input set, summed.

## Inputs
* `sys` – system
* `r` – step size
* `V` – input zonotope

## Output
* the orders of the input solution summed up to a given order
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⊕_{i ≤ η} [Aⁱ r^{i+1}/(i+1)!] V` over every `A ∈ sys.A`, at index `η`. -/
def LinParamSys.inputTaylorSumFloat (sys : LinParamSys ℐ[𝕋] n)
    (r : 𝕋) (V : Zonotope (Vec 𝕋 n)) : ℕ → Zonotope (Vec 𝕋 n)
  | 0 => Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
      (MatExp.intervalInputTerm sys.A r 0) V
  | i + 1 => sys.inputTaylorSumFloat r V i ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋])
      (MatExp.intervalInputTerm sys.A r (i + 1)) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
