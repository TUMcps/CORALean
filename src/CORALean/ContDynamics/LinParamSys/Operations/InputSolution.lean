module

public import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSum
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainder

@[expose] public section

/-!
# The set every input contributes over one step, at a set-valued matrix

[1, Thm. 1] with the system matrix ranging over a set: the orders up to `η` exactly, each an
interval matrix, and everything past `η` in `intervalInputRemainder` — the same remainder that
bounds the exponential of the box. Every factor is an interval matrix here, where the point
case multiplies by a plain matrix for the exact orders. The input set is the state-space
`V = B U ⊕ c` (`inputSet`) that `reachUnion` forms from CORA's `params.U`.

## Inputs
* `sys` – system
* `r` – step size
* `η` – Taylor order
* `U` – input set

## Output
* the set the inputs contribute over one step

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Everything the input can contribute over one step, at every matrix the
system's set holds: `⊕ᵢ Aⁱr^{i+1}/(i+1)! U ⊕ E(r)·r·U`. -/
noncomputable def LinParamSys.inputSolution (sys : LinParamSys ℐ n) (r : ℝ) (η : ℕ)
    (U : S n) : S n :=
  sys.inputTaylorSum r U η ⊞
    Mtimes.mtimes (𝕄 := ℐ) (MatExp.intervalInputRemainder sys.A r η) U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
