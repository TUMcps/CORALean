import CORALean.Global.Tensor

/-!
# The factor a merge's cost scales by

`mergeRowWeight` sums a row of `W`, in absolute value, over *every* neuron rather than over a
bucket, since [1]'s tolerance search must pick `δ` before any bucket exists to sum over.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factor the merge's cost scales by at output `i`: `W`'s row, in absolute
value, over *all* neurons rather than over a bucket not yet chosen. -/
def mergeRowWeight {n n₂ : ℕ} (W : Mat ℝ n₂ n) (i : Fin n₂) : ℝ := ∑ k, |W i k|

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
