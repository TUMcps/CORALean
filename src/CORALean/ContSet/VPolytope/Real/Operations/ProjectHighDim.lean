import CORALean.ContSet.VPolytope.Real.Operations.Map

/-!
# `VPolytope.projectHighDim`

CORA's `@polytope/projectHighDim`, the vertex branch: `V = zeros(N, k); V(dims,:) = P.V`, every
vertex written into the coordinates `dims` of a zero vector. That is `map` at the zero-padding
map, the transpose of the selection matrix, which is linear.

CORA's assignment overwrites on a repeated index where the matrix sums; the statement
`projectHighDim_exact` is an image under the matrix, which is what an injective `dims` gives.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The vertices of `P` zero-padded into the coordinates `dims` of `ℝᴺ`. -/
def VPolytope.projectHighDim (P : VPolytope (Vec ℝ n)) (dims : Fin n → Fin N) :
    VPolytope (Vec ℝ N) :=
  P.map (Matrix.mulVecLin (Matrix.of fun (i : Fin N) (k : Fin n) =>
    if dims k = i then (1 : ℝ) else 0))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
