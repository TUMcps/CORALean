import CORALean.ContSet.Interval.Real.Operations.Tril
import CORALean.ContSet.Interval.Real.Theorems.MaskExact

/-!
# `Interval.tril` is exactly the image under `tril`

CORA's `tril` of an interval matrix takes MATLAB's `tril` of both bounds. For a box with no empty
entry that is the image of the box under `tril` of the matrix, entry by entry.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.tril_exact (K : ℕ) (I : Interval (Mat ℝ m n))
    (hI : ∀ i j, I.inf i j ≤ I.sup i j) :
    (I.tril K).construct = (fun (A : Mat ℝ m n) (i : Fin m) (j : Fin n) =>
      if (j : ℕ) ≤ (i : ℕ) + K then A i j else 0) '' I.construct :=
  Interval.mask_exact _ I hI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
