module

public import CORALean.ContSet.Interval.Float.Operations.Submatrix
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# A submatrix of a matrix in a box lies in the submatrix of the box
Exact, entry by entry: the bounds of the submatrix are the bounds at the chosen rows and columns.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n m' n' : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.submatrix_mem {I : Interval (Mat 𝕋 m n)} {M : Mat ℝ m n} (hM : M ∈ I.construct)
    (r : Fin m' → Fin m) (c : Fin n' → Fin n) :
    M.submatrix r c ∈ (I.submatrix r c).construct :=
  Interval.mem_mat_iff.mpr fun i j => Interval.mem_mat_iff.mp hM (r i) (c j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
