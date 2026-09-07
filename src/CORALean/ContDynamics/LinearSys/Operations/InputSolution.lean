import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSum
import CORALean.ContSet.Interval.Real.Instances

/-!
# The set every input contributes over one step

[1, Thm. 3.1]: the orders up to `η` exactly, and everything past `η` in the
same remainder that bounds the exponential — so the tail costs a second product
rather than a second argument about convergence.

`Mtimes ℐ S` is what the remainder needs: it is an interval matrix, so the
representation must multiply by one of those and not only by a plain matrix.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Althoff's Thm. 3.1: everything the input can contribute over one step,
`⊕ᵢ Aⁱr^{i+1}/(i+1)! U ⊕ E(r)·r·U`. -/
noncomputable def LinearSys.inputSolution
    (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ) (U : S n) : S n :=
  sys.inputTaylorSum r U η ⊞
    Mtimes.mtimes (𝕄 := ℐ) (MatExp.inputRemainder (toRealMat sys.A) r η) U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
