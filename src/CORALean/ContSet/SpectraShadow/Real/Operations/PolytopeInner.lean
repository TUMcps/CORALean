import CORALean.ContSet.VPolytope.Real.VPolytope
import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# `SpectraShadow.polytopeInner`

CORA's `polytope(SpS, 'inner', splits)`, its default: the hull of the points `v` that `[~, v] =
supportFunc(dir)` returns as maximisers along a grid of directions, taken in the shadow shifted by
its `center`, and shifted back. The centre `c` and the maximisers `v` are the solver's, so they are
arguments; `Theorems.PolytopeInner` holds whichever points of the shifted shadow they are. CORA's
`polytope.Inf` when no direction has a maximiser is not modelled: the vertex list is then empty.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.polytopeInner (c : Vec ℝ n) (v : Fin N → Vec ℝ n) : VPolytope (Vec ℝ n) :=
  { k := N, V := fun i => v i + c }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
