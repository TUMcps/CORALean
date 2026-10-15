module

public import CORALean.ContSet.Ellipsoid.Float.Operations.ContainsPoint
public import CORALean.ContSet.Polygon.Float.Operations.Basic
public import CORALean.ContSet.VPolytope.Float.Operations.EnclosePoints

@[expose] public section

/-!
# `Ellipsoid.polygon`, over a floating-point scalar

CORA's `@ellipsoid/polygon` as an inner polygon of a float ellipsoid. A float vertex cannot be
read off the boundary: rounding moves it, and there is no direction to move it that stays inside.
So the caller proposes, for each support direction `l`, the scaled direction
`w = l / √(lᵀ Q l)` (a float `sqrt` and division, unchecked), each gives the vertex `q + Q w`,
CORA's `q + Q l / √(lᵀ Q l)`, rounded up, and a vertex is kept only if `Ellipsoid.containsPoint`
certifies it with its own `w`. That test needs the rounding remainder inside the error box and
`wᵀ Q w ≤ 1` upward, so the `w` are best shrunk slightly. The polygon is the hull of the kept
vertices, with no error box.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polygon spanned by the vertices `q + Q w` that the ellipsoid certifies. -/
def Ellipsoid.polygon (E : Ellipsoid 𝕋 2) (W : List (Vec 𝕋 2)) : Polygon 𝕋 :=
  -- the candidate vertex of a scaled direction `w`: `q + Q w`, rounded up
  let vertex : Vec 𝕋 2 → Vec 𝕋 2 := fun w i => addUp (E.q i) (mulVecUp E.Q w i)
  -- the directions whose vertex `containsPoint` certifies
  let kept : List (Vec 𝕋 2) := W.filter fun w => E.containsPoint (vertex w) w
  let Y : Fin kept.length → Vec 𝕋 2 := fun j => vertex kept[j]
  Polygon.ofPieces [VPolytope.enclosePoints Y]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
