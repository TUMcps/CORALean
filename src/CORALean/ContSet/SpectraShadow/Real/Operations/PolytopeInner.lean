module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.polytopeInner`

CORA's `polytope(SpS, 'inner', splits)`, its default: the hull of the points `v` that `[~, v] =
supportFunc(dir)` returns as maximisers along a grid of directions, taken in the shadow shifted by
its `center`, and shifted back. The center `c` and the maximisers `v` are the solver's, so they are
arguments; `Theorems.PolytopeInner` holds whichever points of the shifted shadow they are. CORA's
`polytope.Inf` when no direction has a maximiser is not modelled: the vertex list is then empty.

## Inputs
* `c` – center of length `n`
* `v` – vectors indexed by `Fin N`

## Output
* the V-polytope with vertices `v i + c`, the maximisers shifted back by the center
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.polytopeInner (c : Vec ℝ n) (v : Fin N → Vec ℝ n) : VPolytope (Vec ℝ n) :=
  { k := N, V := fun i => v i + c }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
