module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Polygon.Real.Operations.OfPieces
public import CORALean.ContSet.VPolytope.Real.Operations.Basic
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `Ellipsoid.polygon`

CORA's `@ellipsoid/polygon`: the polygon of the boundary points `priv_boundary` returns for a
two-dimensional ellipsoid. A boundary point is the support point `q + Q l / sqrt(l'Q l)` of a
direction `l`. The directions `L` are the
argument (CORA's are `N = 1000` equal-area points of the circle, `eq_point_set`), and the polygon
is the one convex piece spanned by the points: CORA's `polyshape` of the same vertices in order is
a boundary representation (R-PG) not modelled. A direction with `l'Q l = 0` gives the center
`q` (Lean's `0⁻¹ = 0`), as does every direction of a point-ellipsoid (CORA's
`representsa_(E,'point')` branch).

## Inputs
* `E` – planar ellipsoid
* `L` – directions

## Output
* polygon spanned by the support points of the directions
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polygon spanned by the support points of the directions `L`. -/
noncomputable def Ellipsoid.polygon (E : Ellipsoid 2) (L : List (Vec ℝ 2)) : Polygon :=
  -- `Y(:,i) = q + Q l / sqrt(l'Q l)` for the `i`-th direction `l`
  let Y : Fin L.length → Vec ℝ 2 := fun i =>
    E.q + (Real.sqrt (L[i] ⬝ᵥ E.Q *ᵥ L[i]))⁻¹ • (E.Q *ᵥ L[i])
  Polygon.ofPieces [VPolytope.enclosePoints Y]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
