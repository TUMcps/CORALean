module

public import CORALean.ContSet.VPolytope.Real.Operations.Bilin

@[expose] public section

/-!
# `VPolytope.mtimesMatPolytope`

CORA's matrix-polytope times a vertex set: `bilin` at `Matrix.mulVecBilin`, the
matrix-vector product read as a bilinear map so a matrix's own vertices pair
with the set's.

## Inputs
* `M` – matrix polytope
* `P` – polytope

## Output
* polytope of products of matrices of `M` with vertices of `P`
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
