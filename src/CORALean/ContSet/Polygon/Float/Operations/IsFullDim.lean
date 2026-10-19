module

public import CORALean.ContSet.Polygon.Float.Operations.OrientBounds
public import CORALean.ContSet.Polygon.Float.Polygon

@[expose] public section

/-!
# `Polygon.isFullDim`, over a floating-point scalar

The region has an interior point when some piece has three vertices that are not collinear and
a nonempty error box. The cross product `(b - a) × (c - a)` is six products of stored
coordinates, bracketed by directed roundings, and certified nonzero by `ltStrict` on one side
of `0`; the box's `inf ≤ sup` by `le`. Only `true` is certain; CORA's count of boundary vertices
(R-PG) is not what is tested.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The cross product of `(b - a, c - a)`, certified on one side of zero. -/
def Polygon.aux_crossCertified (p : VPolytope (Vec 𝕋 2)) (a b c : Fin p.k) : Bool :=
  let D := Polygon.orientBounds (p.V a) (p.V b) (p.V c)
  ltStrict zero D.inf || ltStrict D.sup zero


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Some piece with a nonempty box and three vertices certified not collinear. -/
def Polygon.isFullDim (P : Polygon 𝕋) : Bool :=
  P.sets.any fun p =>
    ((List.finRange 2).all fun i => le (p.I_error.inf i) (p.I_error.sup i)) &&
      (List.finRange p.k).any fun a => (List.finRange p.k).any fun b =>
        (List.finRange p.k).any fun c => Polygon.aux_crossCertified p a b c

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
