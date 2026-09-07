import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.Float.Instances.Dyadic.Instances

/-!
# Dyadics on the page

A dyadic is `m · 2 ^ e`, so it has an exact decimal expansion — of `|e|` places
when `e` is negative, which after a few rounded operations is more places than
anyone reads. So a fixed number of them, rounded *outward*: a lower bound is
floored and an upper bound ceiled, and the box printed therefore contains the
box in memory rather than merely resembling it.

None of this is proved and none of it needs to be. It is the last step, after
every guarantee has been discharged, and it errs in the direction the guarantees
already err in.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Demo

open CORALean CORALean.Float

/-- Decimal places every number below is printed to. Nine, because the error box
starts out around `2 ^ -25` and a table that showed it as `0.000000` would hide
the one quantity the demo exists to display. -/
def places : ℕ := 9

/-- `m · 2 ^ e` scaled by `10 ^ places`, floored or ceiled. Integer `/` on ℤ is
floor division, and a ceiling is the floor of the negation — the same identity
`Dyadic.roundUp` is built on. -/
def scale {p : ℕ} (up : Bool) (d : Dyadic p) : ℤ :=
  let num := d.mantissa * 10 ^ places
  if 0 ≤ d.exponent then num * 2 ^ d.exponent.toNat
  else
    let den : ℤ := 2 ^ (-d.exponent).toNat
    if up then -(-num / den) else num / den

/-- `s / 10 ^ places`, written out. -/
def render (s : ℤ) : String :=
  let a := s.natAbs
  let q := 10 ^ places
  let frac := toString (a % q)
  (if s < 0 then "-" else "") ++ toString (a / q) ++ "." ++
    String.ofList (List.replicate (places - frac.length) '0') ++ frac

/-- Never above the number. -/
def showDown {p : ℕ} (d : Dyadic p) : String := render (scale false d)

/-- Never below it. -/
def showUp {p : ℕ} (d : Dyadic p) : String := render (scale true d)

/-- Right-aligned in `w` columns. -/
def pad (w : ℕ) (s : String) : String :=
  String.ofList (List.replicate (w - s.length) ' ') ++ s

/-- One coordinate of a box, each end rounded away from it. -/
def showBound {p n : ℕ} (I : Interval (Dyadic p) n) (i : Fin n) : String :=
  "[" ++ pad 14 (showDown (I.inf i)) ++ "," ++ pad 15 (showUp (I.sup i)) ++ " ]"

/-- Every coordinate of a box, in order. -/
def showBox {p n : ℕ} (I : Interval (Dyadic p) n) : String :=
  String.intercalate " " (List.ofFn fun i => showBound I i)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The width of one coordinate, rounded up, so the number never understates how
wide the box is. -/
def showWidth {p n : ℕ} (I : Interval (Dyadic p) n) (i : Fin n) : String :=
  showUp (subUp (I.sup i) (I.inf i))

end CORALean.Demo


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
