import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.Interval.Float.Operations.ProjectHighDim

/-!
# `VPolytope.projectHighDim`, over a floating-point scalar

The vertex form of CORA's `projectHighDim`, as over ℝ: each vertex zero-padded into the
coordinates `dims` of the larger space. The padding copies the stored vertices and `0` is exact,
so only the error box needs `Interval.projectHighDim_`, which certifies emptiness in one direction.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.projectHighDim (P : VPolytope 𝕋 n) (dims : Fin n → Fin N) : VPolytope 𝕋 N where
  k := P.k
  V := fun l j =>
    if h : ∃ k, dims k = j then P.V l (Fin.find (fun k => dims k = j) h) else zero
  E := P.E.projectHighDim_ N dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
