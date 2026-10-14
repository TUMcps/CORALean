module

public import CORALean.ContSet.Polygon.Float.Operations.ConvHullOfList
public import CORALean.ContSet.Polygon.Float.Operations.IntervalOfList
public import CORALean.ContSet.Polygon.Float.Polygon
public import CORALean.ContSet.SetUnion.Operations.Plus
public import CORALean.ContSet.VPolytope.Float.Instances
public import CORALean.ContSet.VPolytope.Float.Operations.LinComb
public import CORALean.ContSet.VPolytope.Float.Operations.Mtimes
public import CORALean.ContSet.VPolytope.Float.Operations.Project

@[expose] public section

/-!
# `ContSet/Polygon/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

section

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- ====================================  `Polygon.convHull`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `convHull_` of a polygon, and `polytope(pgon)`, the polytope on the vertices of its hull:
the V-polytope joining every piece's vertex list, with the pieces' error boxes hulled. -/
def Polygon.convHull (P : Polygon 𝕋) : VPolytope (Vec 𝕋 2) :=
  Polygon.convHullOfList P.sets

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  `Polygon.empty`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The empty polygon.

No pieces. -/
def Polygon.empty (𝕋 : Type) [FloatOps 𝕋] : Polygon 𝕋 := ⟨[]⟩


-- ====================================  `Polygon.interval`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The box holding every piece.

The hull of the pieces' boxes (`Interval.or`), the empty box for no pieces. -/
def Polygon.interval (P : Polygon 𝕋) : Interval (Vec 𝕋 2) :=
  Polygon.intervalOfList P.sets


-- ====================================  `Polygon.linComb`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The convex combinations of every pair of pieces, one from each polygon.

Every pair of pieces combined by the float polytope's own `linComb`. -/
def Polygon.linComb (P Q : Polygon 𝕋) : Polygon 𝕋 :=
  ⟨(P.sets ×ˢ Q.sets).map fun pq => (VPolytope.linComb pq.1 pq.2).materialise⟩


-- =====================================  `Polygon.mtimes`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every piece mapped by `M`.

Every piece mapped by the float matrix. -/
def Polygon.mtimes (M : Mat 𝕋 2 2) (P : Polygon 𝕋) : Polygon 𝕋 :=
  ⟨P.sets.map fun p => (VPolytope.mtimes M p).materialise⟩


-- ====================================  `Polygon.ofPieces`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The union of the float convex pieces `pieces`.

The constructor: a polygon from float convex pieces. -/
def Polygon.ofPieces (pieces : List (VPolytope (Vec 𝕋 2))) : Polygon 𝕋 := ⟨pieces⟩


-- =======================================  `Polygon.or`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The union: the pieces of both.

The pieces of both; nothing is computed. -/
def Polygon.or (P Q : Polygon 𝕋) : Polygon 𝕋 := ⟨P.sets ++ Q.sets⟩


-- ======================================  `Polygon.plus`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every pair of pieces, summed.

Every pair of pieces summed by the float polytope's own `plus`. -/
def Polygon.plus (P Q : Polygon 𝕋) : Polygon 𝕋 := SetUnion.plus P Q


-- ====================================  `Polygon.project`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every piece read at the coordinates `dims`.

Every piece read at the coordinates `dims`; also `projectHighDim_` and `lift_` at `N = 2`. -/
def Polygon.project (P : Polygon 𝕋) (dims : Fin 2 → Fin 2) : Polygon 𝕋 :=
  ⟨P.sets.map fun p => VPolytope.project p dims⟩

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
