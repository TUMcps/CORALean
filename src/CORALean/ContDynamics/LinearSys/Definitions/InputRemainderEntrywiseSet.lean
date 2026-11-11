module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainderEntrywise
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# The set a system's entrywise input remainder contributes

`MatExp.inputRemainderEntrywise` at the system's own matrix, times the input set: the
`E(r,η)·r·U` of [1] with the entrywise remainder, the part of `inputSolutionEntrywise`
that comes from the orders past `η`.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `U` – input set

## Output
* set the entrywise remainder, scaled by the step, adds to the input's contribution

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
variable {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set of the system's `inputRemainderEntrywise` times the input set `U`. -/
noncomputable abbrev LinearSys.inputRemainderEntrywiseSet (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ)
    (U : S n) : Set (Vec ℝ n) :=
  toSet (Mtimes.mtimes (𝕄 := ℐ) (MatExp.inputRemainderEntrywise (toRealMat sys.A) r η) U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
