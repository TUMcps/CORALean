import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.Global.Float.Instances.FixedPoint.Instances

/-!
# `FixedPoint`, run: a decimal enclosure of a repeating fraction

`1 / 3` and `1 / 7` have no finite decimal expansion, so at `FixedPoint 4`
`divDown`/`divUp` bracket each with a gap of one digit -- `0.3333`/`0.3334` and
`0.1428`/`0.1429` -- and `Interval.plus` carries that bracket through addition,
`addDown`/`addUp` on the inner and outer edges. Run rather than only proved,
the way `Examples/RunnableFloat.lean` runs the other representations:
`divDown_le_div`/`le_divUp`/`PlusOuter` (Theorems) are what makes each `#eval`
below an enclosure and not merely a number.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.FixedPointDemo

open CORALean CORALean.Float FloatOps

/-- Four fractional digits: enough to see `1 / 3`, `1 / 7` and their sum are
each bracketed rather than landed on exactly. -/
abbrev D := FixedPoint 4

def one : D := ⟨1, 0⟩
def three : D := ⟨3, 0⟩
def seven : D := ⟨7, 0⟩

/-- `[0.3333, 0.3334] ⊇ {1 / 3}`. -/
def third : Interval (Vec D 1) := ⟨fun _ => divDown one three, fun _ => divUp one three⟩

/-- `[0.1428, 0.1429] ⊇ {1 / 7}`. -/
def seventh : Interval (Vec D 1) := ⟨fun _ => divDown one seven, fun _ => divUp one seven⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `1 / 3 + 1 / 7 = 10 / 21 = 0.476190…`, and `Interval.plus` rounds each edge
outward again, so the printed bracket still encloses it after one more
operation. -/
def sum : Interval (Vec D 1) := Interval.plus third seventh

#eval (third.inf 0).m -- 3333, at 4 digits: 0.3333 ≤ 1/3
#eval (third.sup 0).m -- 3334, at 4 digits: 1/3 ≤ 0.3334
#eval (seventh.inf 0).m -- 1428, at 4 digits: 0.1428 ≤ 1/7
#eval (seventh.sup 0).m -- 1429, at 4 digits: 1/7 ≤ 0.1429
#eval (sum.inf 0).m -- 4761, at 4 digits: 0.4761 ≤ 10/21
#eval (sum.inf 0).d
#eval (sum.sup 0).m -- 4763, at 4 digits: 10/21 ≤ 0.4763
#eval (sum.sup 0).d

end CORALean.FixedPointDemo


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
