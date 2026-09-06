import CORALean.ContSet.VPolytope.Real.Operations.Bilin

/-!
# `VPolytope.mtimesMatPolytope`

CORA's matrix-polytope times a vertex set: `bilin` at `Matrix.mulVecBilin`, the
matrix-vector product read as a bilinear map so a matrix's own vertices pair
with the set's.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def VPolytope.mtimesMatPolytope (M : VPolytope (Mat ℝ m n))
    (P : VPolytope (Vec ℝ n)) : VPolytope (Vec ℝ m) :=
  VPolytope.bilin (Matrix.mulVecBilin ℝ ℝ) M P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
