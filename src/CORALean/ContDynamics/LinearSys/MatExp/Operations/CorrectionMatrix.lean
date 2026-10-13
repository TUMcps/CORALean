import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

/-!
# The correction matrix

`correctionMatrix`: the `F` of [1]: the orders up to `η` exactly, everything past `η` in the
same remainder that bounds the exponential, and indexed from `2`, the constant and linear
terms of the interpolation error cancelling.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F` of [1]: the orders up to `η` exactly, everything past `η` in the same
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
