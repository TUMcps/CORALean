import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSum
import CORALean.ContDynamics.LinearSys.MatExp.IntervalCorrection

/-!
# The set every input contributes over one step, at a set-valued matrix

[1, Thm. 3.1] with the system matrix ranging over a set: the orders up to `η`
exactly, each an interval matrix, and everything past `η` in
`intervalInputRemainder` — the same remainder that bounds the exponential of
the box, so the tail costs a second product rather than a second argument about
convergence.

Every factor is an interval matrix here, where the point case multiplies by a
plain matrix for the exact orders and by an interval one for the tail alone.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


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
