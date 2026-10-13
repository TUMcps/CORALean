import CORALean.ContSet.Ellipsoid.Float.Operations.ContainsPoint
import CORALean.ContSet.Polygon.Float.Operations.OfPieces
import CORALean.ContSet.VPolytope.Float.Operations.EnclosePoints

/-!
# `Ellipsoid.polygon`, over a floating-point scalar

CORA's `@ellipsoid/polygon` as an inner polygon of a float ellipsoid. A float vertex cannot be
read off the boundary: rounding moves it, and there is no direction to move it that stays inside.
So the caller proposes the unit factors `u = Gᵀ l / ‖Gᵀ l‖₂` of the support points (a float
`sqrt` and division, unchecked), each gives the vertex `q + G u` rounded up, and a vertex is kept
only if `Ellipsoid.containsPoint` certifies it with its own factor. That test needs the rounding
remainder inside the error box and `‖u‖₂ ≤ 1` upward, so factors are best shrunk slightly. The
polygon is the hull of the kept vertices, with no error box.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polygon spanned by the vertices of the factors that the ellipsoid certifies. -/
def Ellipsoid.polygon (E : Ellipsoid 𝕋 2) (U : List (Vec 𝕋 E.k)) : Polygon 𝕋 :=
  -- the candidate vertex of a factor `u`: `q + G u`, rounded up
  let vertex : Vec 𝕋 E.k → Vec 𝕋 2 := fun u i => addUp (E.q i) (dotUp (fun j => E.G i j) u)
  -- the factors whose vertex `containsPoint` certifies
  let kept : List (Vec 𝕋 E.k) := U.filter fun u => E.containsPoint (vertex u) u
  let Y : Fin kept.length → Vec 𝕋 2 := fun j => vertex kept[j]
  Polygon.ofPieces [VPolytope.enclosePoints Y]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
