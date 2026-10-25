module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumFloat

@[expose] public section

/-!
# The set every input contributes over one step, in floats

`inputSolution` [1, Thm. 1] computed in `𝕋`: the orders up to `η` by
`inputTaylorSumFloat`, and everything past `η` in
`MatExp.intervalInputRemainder`, the float `E(r)·r` taken at the bound
`normUpperBound (r • A)` the exponential and the correction of the same step are
taken at — so the order `reachOrderFloat` admits for those admits this too.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `V` – float input zonotope

## Output
* float zonotope of everything the input contributes over one step

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
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

/-- [1, Thm. 1] in floats: `⊕ᵢ [Aⁱr^{i+1}/(i+1)!] V ⊕ [E(r)·r] V`. -/
def LinearSys.inputSolutionFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ) (V : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 n) :=
  sys.inputTaylorSumFloat r V η ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋])
    (MatExp.intervalInputRemainder (Interval.point sys.A) r η) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
