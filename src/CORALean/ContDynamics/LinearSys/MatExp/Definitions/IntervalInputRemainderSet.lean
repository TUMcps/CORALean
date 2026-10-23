module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainder
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# The set the input remainder of a box contributes

The interval matrix `intervalInputRemainder` of a box of system matrices, multiplied onto an input
set: the `E(r)·r·U` over the whole box ([1, Sec. 4.4]), the part of `inputSolutionZono` that comes
from the orders past `η`.

## Inputs
* `A` – interval matrix of system matrices
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
open Matrix ContSet

variable {n : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set of `intervalInputRemainder` times the input set `U`. -/
noncomputable abbrev MatExp.intervalInputRemainderSet (A : Interval (Mat ℝ n n)) (r : ℝ) (η : ℕ)
    (U : S n) : Set (Vec ℝ n) :=
  construct (Mtimes.mtimes (𝕄 := ℐ) (MatExp.intervalInputRemainder A r η) U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
