import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Theorems.AndOuter
import CORALean.ContSet.Zonotope.Float.Theorems.CentreMemConstruct
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef
import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

/-!
# Intersecting two float zonotopes

CORA's `and_` at `Zonotope`, `Dyadic 53`: a square `[-1, 1]²` and a diamond `|x| + |y| ≤ 3/2`,
intersected through constrained zonotopes and enclosed again by a zonotope. The diamond cuts
the square's four corners off, so the intersection is an octagon, which needs four
generators; the answer has them. The hull of the answer is printed; `Zonotope.and_outer` says the
intersection lies inside it, and the origin, a point of both, is shown to be in the
answer.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.AndZonotopeFloat

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


/-- The square `[-1, 1]²` and the diamond `|x| + |y| ≤ 3/2`, both centred at the origin. -/
def square : Zonotope (Vec D 2) := ⟨2, ![d 0 0, d 0 0], ![![d 1 0, d 0 0], ![d 0 0, d 1 0]], box0⟩
def diamond : Zonotope (Vec D 2) :=
    ⟨2, ![d 0 0, d 0 0], ![![d 3 (-2), d 3 (-2)], ![d 3 (-2), d (-3) (-2)]], box0⟩


-- =====================================  MAIN DEFINITION  ====================================== --

def squareDiamond : Zonotope (Vec D 2) := square.and_ diamond

#eval squareDiamond.h
#eval boxF squareDiamond.interval   -- the hull of the answer

/-- Both zonotopes have no error, so their centres are points of them. -/
theorem centre_mem (Z : Zonotope (Vec D 2)) (h : Z.I_error = box0) : toRealVec Z.c ∈ Z.construct :=
  Zonotope.centre_mem_construct Z fun i => by simp only [h, box0, toReal_d]; norm_num

/-- The origin is in both, hence in the answer. -/
theorem origin_mem : toRealVec square.c ∈ squareDiamond.construct :=
  Zonotope.and_outer square diamond ⟨centre_mem square rfl, by
    have : toRealVec square.c = toRealVec diamond.c := rfl
    rw [this]; exact centre_mem diamond rfl⟩

/-- Everything in both lies in the answer. -/
theorem squareDiamond_outer : square.construct ∩ diamond.construct ⊆ squareDiamond.construct :=
  Zonotope.and_outer square diamond

end CORALean.Examples.AndZonotopeFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
