module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainderEntrywise
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSum
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# The set every input contributes over one step, as CORA computes it

`inputSolutionEntrywise`: the orders up to `η` exactly, each as a term of its own, and everything
past `η` in the entrywise `E(Δt,η)·Δt` [1] (CORA's `particularSolution_timeVarying`).
It is `inputSolution` with the scalar remainder bound replaced by the entry's own.

`Mtimes ℐ S` is what the remainder needs: it is an interval matrix, so the representation must
multiply by one of those and not only by a plain matrix.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `U` – input set

## Output
* set of everything the input contributes over one step

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet ContSetLike Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The orders `0 … η` exactly, `⊕ᵢ Aⁱr^{i+1}/(i+1)! U`, and the tail in `E(r,η)·r·U`. -/
noncomputable def LinearSys.inputSolutionEntrywise
    (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ) (U : S n) : S n :=
  sys.inputTaylorSum r U η ⊞
    Mtimes.mtimes (𝕄 := ℐ) (MatExp.inputRemainderEntrywise (toRealMat sys.A) r η) U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
