import CORALean.ContSet.EmptySet.Real.Theorems.AndExact
import CORALean.ContSet.Fullspace.Real.Theorems.Basic
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.Global.Float.Instances.Dyadic.Instances

/-!
# The two trivial intersections

`EmptySet.and_` and `Fullspace.and_`: `∅ ∩ s = ∅` and `univ ∩ s = s` for a set `s` of any
representation (here a float zonotope, the unit square), exactly (`EmptySet.and_exact`,
`Fullspace.and_exact`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.AndEmptyFullspace

open CORALean CORALean.Float FloatOps SoundFloatArithmetic

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

theorem toReal_d (m e : ℤ) : toReal (d m e) = (m : ℝ) * 2 ^ e := Dyadic.toReal_def _

/-- No rounding error. -/
def box0 : Interval (Vec D 2) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The unit square `[-1, 1]²`. -/
def square : Zonotope (Vec D 2) := ⟨2, ![d 0 0, d 0 0], ![![d 1 0, d 0 0], ![d 0 0, d 1 0]], box0⟩

/-- `∅ ∩ s = ∅`, for a float zonotope `s`. -/
example (E : Real.EmptySet 2) :
    ContSet.construct (E.and_ square) = ContSet.construct E ∩ ContSet.construct square :=
  Real.EmptySet.and_exact E square

/-- `univ ∩ s = s`, for a float zonotope `s`. -/
example (F : Real.Fullspace 2) :
    ContSet.construct (F.and_ square) = F.construct ∩ ContSet.construct square :=
  Real.Fullspace.and_exact F square

end CORALean.Examples.AndEmptyFullspace


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
