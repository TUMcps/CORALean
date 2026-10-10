import CORALean.ContSet.Polygon.Float.Operations.InTriangle
import CORALean.ContSet.VPolytope.Float.VPolytope

/-!
# `Polygon.pieceHolds`

A float point lies in the hull of a piece's stored vertices (the nominal piece, without its
error box): in the plane a point of a hull lies in a triangle of three of the vertices
(Carathéodory), so every triple of vertices is tried with `Polygon.inTriangle`. Only `true` is
certain; a point on an edge or too close to one for the rounding answers `false`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.pieceHolds (p : VPolytope 𝕋 2) (x : Vec 𝕋 2) : Bool :=
  (List.finRange p.k).any fun a => (List.finRange p.k).any fun b =>
    (List.finRange p.k).any fun c =>
      Polygon.inTriangle (p.V a) (p.V b) (p.V c) x

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
