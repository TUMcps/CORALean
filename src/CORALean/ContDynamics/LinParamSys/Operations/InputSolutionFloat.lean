module

public import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat

@[expose] public section

/-!
# What the input contributes over one step at every member, in floats

`LinParamSys.inputSolution` computed in `𝕋`: the Taylor orders up to `η`, and the
remainder `[E(r)·r]` over the whole box `sys.A`, `MatExp.intervalInputRemainder`
at `sys.A` itself, times the input set.

## Inputs
* `sys` – system
* `r` – step size
* `η` – Taylor order
* `V` – input zonotope

## Output
* the zonotope the inputs contribute over one step

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
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

/-- [1, Thm. 1] in floats over every `A ∈ sys.A`: `⊕ᵢ [Aⁱr^{i+1}/(i+1)!] V ⊕ [E(r)·r] V`. -/
def LinParamSys.inputSolutionFloat (sys : LinParamSys ℐ[𝕋] n)
    (r : 𝕋) (η : ℕ) (V : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  sys.inputTaylorSumFloat r V η ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋])
    (MatExp.intervalInputRemainder sys.A r η) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
