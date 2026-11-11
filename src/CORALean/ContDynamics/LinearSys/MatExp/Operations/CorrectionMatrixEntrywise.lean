module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderEntrywise

@[expose] public section

/-!
# `MatExp.correctionMatrixEntrywise`, the correction `F` of CORA

`correctionMatrixEntrywise`: the `F` of CORA's `priv_correctionMatrixState`: the orders `2`
through `η` as in `correctionMatrix` [2, Thm. 3], and everything past `η` in the entrywise
`E(r,η)` of [1] where `correctionMatrix` [2, Thm. 3] takes one radius for every entry. Every term of
the tail is under `rⁱ/i!` against `|A|ⁱ`, so the tail needs no condition on `η`.

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
* [2] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". Proceedings of the IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of CORA: the orders up to `η` exactly, the tail in the entrywise remainder `E(r,η)`. -/
noncomputable def MatExp.correctionMatrixEntrywise (A : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range (η - 1), min (MatExp.corrTerm A r (i + 2) j k) 0)
    - MatExp.expRemainderMat A r η j k
  sup := fun j k => (∑ i ∈ Finset.range (η - 1), max (MatExp.corrTerm A r (i + 2) j k) 0)
    + MatExp.expRemainderMat A r η j k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
