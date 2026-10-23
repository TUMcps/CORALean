module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.InputRemainderSet
public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# The set a system's input remainder contributes

`MatExp.inputRemainderSet` at the system's own matrix: the `E(r)·r·U` of [1, Thm. 1], the part of
`inputSolution` that comes from the orders past `η`.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `U` – input set

## Output
* set the exponential's remainder, scaled by the step, adds to the input's contribution

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set of the system's `inputRemainder` times the input set `U`. -/
noncomputable abbrev LinearSys.inputRemainderSet (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (U : S n) : Set (Vec ℝ n) :=
  MatExp.inputRemainderSet (toRealMat sys.A) r η U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
