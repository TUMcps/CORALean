module

public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.ContractHalfspace
public import CORALean.ContSet.Polygon.Float.Operations.InnerHRep
public import CORALean.ContSet.Polygon.Float.Operations.PieceSubset
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Polygon.Float.Polygon

@[expose] public section

/-!
# `Polygon.subtract`, over a floating-point scalar

The regularized difference of two polygons as a polygon again: the minuend's pieces, taken
through the subtrahend's pieces one after another, each step replacing a piece `r` by the
pieces of `Polygon.aux_subtractPiece q r`. A piece the subtrahend's piece certainly covers is
dropped, and one with a certified inner halfspace description (`Polygon.innerHRep`) is cut
along its edges, so the pieces exclude the inner description's interior; any other piece is
kept whole. The cut pieces are box hulls, so they may leave the minuend, and the result is an
outer approximation of the region `closure (interior P₁ \ P₂)`, not a subset of `P₁`.

## Inputs
* `P` – polygon
* `Q` – polygon

## Output
* the pieces of `P`, each cut by every piece of `Q` in turn
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The pieces that cover `r \ q`. -/
def Polygon.aux_subtractPiece (q r : VPolytope (Vec 𝕋 2)) : List (VPolytope (Vec 𝕋 2)) :=
  if Polygon.pieceSubset r q then []
  else match Polygon.innerHRep q with
    | some H =>
      if H.me = 0 then
        (List.finRange H.m).map fun i =>
          Interval.vPolytope (r.interval.contractHalfspace (-(H.A i)) (neg (H.b i)))
      else [r]
    | none => [r]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pieces of `P`, each cut by every piece of `Q` in turn. -/
def Polygon.subtract (P Q : Polygon 𝕋) : Polygon 𝕋 :=
  ⟨P.sets.flatMap fun p =>
    Q.sets.foldl (fun L q => L.flatMap (Polygon.aux_subtractPiece q)) [p]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
