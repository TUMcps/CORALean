import CORALean.ContSet.Conversion.Float.Operations.Basic
import CORALean.ContSet.Polygon.Float.Theorems.AndOuter
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.ContSet.Conversion.Real.Operations.Basic

/-!
# Intersecting two float polygons

`Polygon.and`: every pair of pieces intersected by the float `VPolytope.intersection` (through
the pieces' boxes). A square `[0, 2]²` and a triangle with corners `(1, 1)`, `(3, 1)`,
`(1, 3)` give one piece, printed as its box (the float box of a vertex list is the hull of
the vertices, here `[1, 2]²`); `Polygon.and_outer` says the intersection of the polygons
lies inside the answer.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.AndPolygonFloat

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

theorem toReal_d (m e : ℤ) : toReal (d m e) = (m : ℝ) * 2 ^ e := Dyadic.toReal_def _

/-- A scalar read through `Float`, for printing. -/
def toF (x : D) : Float := Float.scaleB (Float.ofInt x.mantissa) x.exponent

/-- No rounding error. -/
def box0 : Interval (Vec D 2) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

/-- A box as `(lo₁, hi₁), (lo₂, hi₂)`. -/
def boxF (I : Interval (Vec D 2)) : (Float × Float) × (Float × Float) :=
  ((toF (I.inf 0), toF (I.sup 0)), (toF (I.inf 1), toF (I.sup 1)))


/-- A vertex list with no rounding error. -/
def poly (h : ℕ) (V : Fin h → Vec D 2) : VPolytope (Vec D 2) := ⟨h, V, box0⟩

/-- The square `[0, 2]²` and a triangle with corners `(1, 1)`, `(3, 1)`, `(1, 3)`. -/
def P : Polygon D :=
  ⟨[poly 4 ![![d 0 0, d 0 0], ![d 2 0, d 0 0], ![d 2 0, d 2 0], ![d 0 0, d 2 0]]]⟩
def Q : Polygon D := ⟨[poly 3 ![![d 1 0, d 1 0], ![d 3 0, d 1 0], ![d 1 0, d 3 0]]]⟩


-- =====================================  MAIN DEFINITION  ====================================== --

def PQ : Polygon D := Polygon.and P Q

#eval PQ.sets.length                          -- 1 piece
#eval PQ.sets.map fun V => boxF V.interval    -- its box, [1, 2]²

theorem PQ_outer : ContSet.construct P ∩ ContSet.construct Q ⊆ ContSet.construct PQ :=
  Polygon.and_outer P Q

end CORALean.Examples.AndPolygonFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
