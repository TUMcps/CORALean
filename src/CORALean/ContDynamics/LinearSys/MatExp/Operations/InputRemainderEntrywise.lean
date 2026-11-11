module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderEntrywise

@[expose] public section

/-!
# The entrywise remainder, scaled by a step

`inputRemainderEntrywise`: the `E(Δt,η)·Δt` of [1], what the orders past `η` contribute to
an input solution over a step, with the entrywise `E(Δt,η)` of `expRemainderEntrywise` where
`inputRemainder` has one radius for every entry. It is CORA's `E*timeStep` in
`particularSolution_timeVarying`.

## Inputs
* `A` – system matrix
* `Δt` – step length
* `η` – Taylor order

## Output
* interval matrix of the scaled remainder, entry by entry

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[-E(Δt,η)·Δt, E(Δt,η)·Δt]`, entry by entry. -/
noncomputable def MatExp.inputRemainderEntrywise (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun j k => -(Δt * MatExp.expRemainderMat A Δt η j k)
  sup := fun j k => Δt * MatExp.expRemainderMat A Δt η j k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
