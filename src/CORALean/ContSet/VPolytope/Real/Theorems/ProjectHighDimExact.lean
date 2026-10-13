import CORALean.ContSet.VPolytope.Real.Operations.ProjectHighDim
import CORALean.ContSet.VPolytope.Real.Theorems.MapExact

/-!
# `projectHighDim` is the zero-padded image, exactly

The vertex form pads each vertex and so denotes the image of `P` under the padding matrix.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.projectHighDim_exact (P : VPolytope (Vec ℝ n)) (dims : Fin n → Fin N) :
    (P.projectHighDim dims).construct
      = (fun y => (Matrix.of fun (i : Fin N) (k : Fin n) =>
          if dims k = i then (1 : ℝ) else 0) *ᵥ y) '' P.construct :=
  (VPolytope.map_exact _ P).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
