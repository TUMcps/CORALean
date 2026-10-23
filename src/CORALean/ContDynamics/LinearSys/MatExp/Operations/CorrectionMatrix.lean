module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

@[expose] public section

/-!
# The correction matrix

`correctionMatrix`: the `F` of [1, Thm. 3]: the orders up to `η` exactly, everything past `η` in the
same remainder that bounds the exponential, and indexed from `2`, the constant and linear
terms of the interpolation error cancelling.

## Inputs
* `A` – system matrix
* `r` – step length
* `η` – Taylor order

## Output
* interval matrix of the correction

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". In Proc. of the 46th IEEE Conference on Decision and Control (CDC),
      2007, pp. 726-732.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of [1, Thm. 3]: the orders up to `η` exactly, everything past `η` in the same
remainder that bounds the exponential, and indexed from `2`, the constant and
linear terms of the interpolation error cancelling. -/
noncomputable def MatExp.correctionMatrix (A : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range (η - 1), min (MatExp.corrTerm A r (i + 2) j k) 0)
    - MatExp.expRemainderBound (r • A) η
  sup := fun j k => (∑ i ∈ Finset.range (η - 1), max (MatExp.corrTerm A r (i + 2) j k) 0)
    + MatExp.expRemainderBound (r • A) η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
