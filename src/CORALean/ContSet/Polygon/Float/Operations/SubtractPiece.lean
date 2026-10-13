import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope
import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval
import CORALean.ContSet.Interval.Float.Operations.ContractHalfspace
import CORALean.ContSet.Polygon.Float.Operations.InnerHRep
import CORALean.ContSet.Polygon.Float.Operations.PieceSubset

/-!
# `Polygon.subtractPiece`

What is left of one convex piece `r` once one convex piece `q` is taken away, as a list of
pieces. Nothing is left when `q` certainly covers `r` (`Polygon.pieceSubset`). Otherwise, if
`q` has a certified inner halfspace description `{x : aᵢᵀx ≤ bᵢ}` (`Polygon.innerHRep`), a point
of `r` outside `q` is outside that description, so it violates some row, `aᵢᵀx ≥ bᵢ`: `r` is
replaced by one piece per row, the box hull of `r` cut to `-aᵢᵀx ≤ -bᵢ` by
`Interval.contractHalfspace`. Without such a description `r` is kept whole.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pieces that cover `r \ q`. -/
def Polygon.subtractPiece (q r : VPolytope 𝕋 2) : List (VPolytope 𝕋 2) :=
  if Polygon.pieceSubset r q then []
  else match Polygon.innerHRep q with
    | some H =>
      if H.me = 0 then
        (List.finRange H.m).map fun i =>
          Interval.vPolytope (r.interval.contractHalfspace (fun j => neg (H.A i j)) (neg (H.b i)))
      else [r]
    | none => [r]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
