module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainder
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# The set the input remainder contributes

The interval matrix `inputRemainder`, multiplied onto an input set: the `E(r)·r·U` of
[1, Thm. 1], the part of `inputSolution` that comes from the orders past `η`.

## Inputs
* `A` – system matrix
* `r` – step length
* `η` – Taylor order
* `U` – input set

## Output
* set the exponential's remainder, scaled by the step, adds to the input's contribution

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
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

/-- The set of `inputRemainder` times the input set `U`. -/
noncomputable abbrev MatExp.inputRemainderSet (A : Mat ℝ n n) (r : ℝ) (η : ℕ) (U : S n) :
    Set (Vec ℝ n) :=
  construct (Mtimes.mtimes (𝕄 := ℐ) (MatExp.inputRemainder A r η) U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
