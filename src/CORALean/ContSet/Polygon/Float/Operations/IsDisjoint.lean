module

public import CORALean.ContSet.HPolytope.Float.Operations.RowLin
public import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
public import CORALean.ContSet.Polygon.Float.Polygon

@[expose] public section

/-!
# `Polygon.isDisjoint`, over a floating-point scalar

The negation of CORA's `@polygon/isIntersecting_` for two polygons, at the region: every pair of
pieces is separated by a line. In the plane two disjoint compact convex sets are separated by
a normal of one of their edges, so the candidate directions are the vertex differences of both
pieces turned by a right angle (rounding is harmless, any direction is a valid try); a
direction `d` separates when the upper bound of `d · x` over the first piece (`boundDot`,
vertices and error box) is certified by `ltStrict` below the lower bound over the second. Only
`true` is certain; CORA's tolerance and the point and other-set operands are not covered.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.isDisjoint (P Q : Polygon 𝕋) : Bool :=
  -- every vertex difference of a piece, turned by a right angle
  let normals : VPolytope (Vec 𝕋 2) → List (Vec 𝕋 2) := fun r =>
    (List.finRange r.k).flatMap fun l => (List.finRange r.k).map fun m =>
      ![subDown (r.V l 1) (r.V m 1), subDown (r.V m 0) (r.V l 0)]
  -- `d` keeps `p` certainly below `q`
  let separates : VPolytope (Vec 𝕋 2) → VPolytope (Vec 𝕋 2) → Vec 𝕋 2 → Bool := fun p q d =>
    let negD : Vec 𝕋 2 := (-d)
    let hiP := (p.boundDot (c := rowLin (fun _ : Fin 1 => d) 0) d fun _ => rfl).val
    let hiQ := (q.boundDot (c := rowLin (fun _ : Fin 1 => negD) 0) negD fun _ => rfl).val
    ltStrict hiP (neg hiQ)
  P.sets.all fun p => Q.sets.all fun q => (normals p ++ normals q).any (separates p q)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
