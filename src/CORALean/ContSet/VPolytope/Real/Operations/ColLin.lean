import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# `colLin`

A vector as an `n × 1` matrix, linearly: the embedding `matPolytope` maps each vertex by.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reshape(V,[dim(P),1,size(V,2)])` slice by slice. -/
def colLin (n : ℕ) : Vec ℝ n →ₗ[ℝ] Mat ℝ n 1 where
  toFun v := fun i _ => v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
