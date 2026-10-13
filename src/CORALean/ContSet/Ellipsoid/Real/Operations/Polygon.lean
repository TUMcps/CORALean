import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Polygon.Real.Operations.OfPieces
import CORALean.ContSet.VPolytope.Real.Operations.EnclosePoints
import CORALean.Global.EuclideanNorm

/-!
# `Ellipsoid.polygon`

CORA's `@ellipsoid/polygon`: the polygon of the boundary points `priv_boundary` returns for a
two-dimensional ellipsoid. A boundary point is the support point `Q l / sqrt(l'Q l)` of a unit
direction `l`; with `Q = G Gᵀ` it is `q + G (Gᵀ l / ‖Gᵀ l‖₂)`. The directions `L` are the
argument (CORA's are `N = 1000` equal-area points of the circle, `eq_point_set`), and the polygon
is the one convex piece spanned by the points: CORA's `polyshape` of the same vertices in order is
a boundary representation (R-PG) not modelled. A direction with `Gᵀ l = 0` gives the centre
`q`, as does every direction of a point-ellipsoid (CORA's `representsa_(E,'point')` branch).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polygon spanned by the support points of the directions `L`. -/
noncomputable def Ellipsoid.polygon (E : Ellipsoid 2) (L : List (Vec ℝ 2)) : Polygon :=
  -- `Y(:,i) = q + G (Gᵀ l / ‖Gᵀ l‖₂)` for the `i`-th direction `l`
  let Y : Fin L.length → Vec ℝ 2 := fun i =>
    E.q + E.G *ᵥ (‖E.Gᵀ *ᵥ L[i]‖₂⁻¹ • (E.Gᵀ *ᵥ L[i]))
  Polygon.ofPieces [VPolytope.enclosePoints Y]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
