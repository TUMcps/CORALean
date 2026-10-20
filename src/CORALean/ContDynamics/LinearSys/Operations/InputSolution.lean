module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainder
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSum
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# The set every input contributes over one step

[1, Thm. 1]: the orders up to `η` exactly, and everything past `η` in the
same remainder that bounds the exponential — so the tail costs a second product
rather than a second argument about convergence.

`Mtimes ℐ S` is what the remainder needs: it is an interval matrix, so the
representation must multiply by one of those and not only by a plain matrix.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `U` – input set

## Output
* set of everything the input contributes over one step

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 1]: everything the input can contribute over one step,
`⊕ᵢ Aⁱr^{i+1}/(i+1)! U ⊕ E(r)·r·U`. -/
noncomputable def LinearSys.inputSolution
    (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ) (U : S n) : S n :=
  sys.inputTaylorSum r U η ⊞
    Mtimes.mtimes (𝕄 := ℐ) (MatExp.inputRemainder (toRealMat sys.A) r η) U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
