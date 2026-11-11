module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderEntrywise

@[expose] public section

/-!
# `MatExp.constCorrectionMatrixEntrywise`, the input correction `G` of CORA

`constCorrectionMatrixEntrywise`: the `G` of CORA's `priv_correctionMatrixInput`: the orders `1`
through `η` as in `constCorrectionMatrix` [2, Sec. III-A], and everything past `η` in `E(r,η)·r`
with the entrywise `E(r,η)` of [1] where `constCorrectionMatrix` takes one radius for every entry.

## Inputs
* `A` – system matrix
* `r` – step length
* `η` – Taylor order

## Output
* interval matrix of the correction

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
* [2] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `G` of CORA: the orders up to `η` exactly, the tail in `E(r,η)·r`, entry by entry. -/
noncomputable def MatExp.constCorrectionMatrixEntrywise (A : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range η, min (MatExp.constCorrTerm A r i j k) 0)
    - r * MatExp.expRemainderMat A r η j k
  sup := fun j k => (∑ i ∈ Finset.range η, max (MatExp.constCorrTerm A r i j k) 0)
    + r * MatExp.expRemainderMat A r η j k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
