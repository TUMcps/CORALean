module

public import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumTailFloat
public import CORALean.ContDynamics.LinParamSys.Operations.Canonical
public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.MatPow
public import CORALean.ContSet.Zonotope.Float.Operations.MatSmul
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContDynamics.LinParamSys.Operations.InputTermZonoFloat

@[expose] public section

/-!
# The set every input contributes over one step, at a float matrix zonotope

`LinParamSys.inputSolutionZono` computed in `𝕋` [1, Thm. 1]: orders `0` and `1` through
the system's float matrix zonotope (`inputTermZonoFloat`), orders `2 … η` and the remainder
`[E(r)·r]` over the interval matrix it encloses, `sys.A.matInterval`. The four pieces stay
four products, as in CORA's `priv_inputSolution`.

## Inputs
* `sys` – system
* `r` – step size
* `η` – Taylor order
* `V` – input zonotope

## Output
* the zonotope the inputs contribute over one step

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


section
variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


end


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 1] in floats: `A_Z r U ⊕ A_Z r²/2! U`, then orders `2 … η` and the remainder
over `A_Z`'s interval matrix. -/
def LinParamSys.inputSolutionZonoFloat (sys : LinParamSys 𝕄𝒵[𝕋] n)
    (r : 𝕋) (η : ℕ) (V : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let IA := sys.A.matInterval                                             -- A_Z's interval matrix
  Mtimes.mtimes (𝕄 := 𝕄𝒵[𝕋]) (S := 𝒵[𝕋])
    (sys.inputTermZonoFloat r 0) V ⊞
    Mtimes.mtimes (𝕄 := 𝕄𝒵[𝕋]) (S := 𝒵[𝕋])
      (sys.inputTermZonoFloat r 1) V ⊞
    (LinParamSys.canonical (𝕄 := ℐ[𝕋]) IA).inputTaylorSumTailFloat r V η ⊞
    Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
      (MatExp.intervalInputRemainder IA r η) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
