import CORALean.ContSet.Polygon.Real.Polygon

/-!
# `Polygon.subtract`

CORA's `polygon/subtract` is MATLAB's `subtract(pgon1.set, pgon2.set)` on `polyshape`s: the
boolean difference of the two regions, regularized (the lower-dimensional remainder of a
difference is dropped, the boundary kept). The set difference of two unions of convex pieces is
not a union of convex pieces as it stands, but its regularization is a region all the same: the
closure of what is left, `closure (interior P₁ \ P₂)`. So the result is the region, not a
`Polygon`; no convex decomposition of it is computed (R-PG), and `polyshape`'s tolerance for
near-coincident boundaries is not modelled.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The regularized difference of the regions of `P₁` and `P₂`. -/
def Polygon.subtract (P₁ P₂ : Polygon) : Set (Vec ℝ 2) :=
  closure (interior (ContSet.construct P₁) \ ContSet.construct P₂)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
