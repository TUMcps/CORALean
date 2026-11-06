module

public import CORALean.Global.Float.Tan
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Interval.tan`

CORA's `@interval/tan`. The tangent increases on every range holding no pole `kπ + π/2`, so the
bounds are `tanDown` at the lower end and `tanUp` at the upper one (`Global/Float/Tan`); a range
that may hold a pole gives `(-∞, ∞)`, hence the `Interval.EBox`. The test needs no enclosure of
`π`: on `[l, u]` the cosine is certified of one strict sign at both ends (`cosDown` positive or
`cosUp` negative) and `u - l`, rounded up, is below `piBelow ≤ π`; a cosine of one sign at both
ends of a range shorter than `π` has no zero between (`Interval.tan_outer`). Otherwise the
coordinate is unbounded, also where a pole is only not excluded by the rounding. Without the test
a box over a pole gave inverted bounds (`Interval.tanPrincipal`). `p` is the halving count.

## Inputs
* `p` – halving count
* `I` – interval box

## Output
* interval box enclosing the tangent of `I`
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   03-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Bounds `tan` is certified bounded by on `[l, u]`: the cosine of one strict sign at both ends and
a range shorter than `piBelow`. The sign is the second component, `true` for a positive cosine. -/
@[step_of Interval.tan]
def Interval.step_tanBranch (p : ℕ) (l u : 𝕋) : Option Bool :=
  if ltStrict (subUp u l) piBelow = true then
    if ltStrict zero (cosDown p l) = true ∧ ltStrict zero (cosDown p u) = true then some true
    else if ltStrict (cosUp p l) zero = true ∧ ltStrict (cosUp p u) zero = true then some false
    else none
  else none


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `interval/tan`: `tanDown` at the lower end and `tanUp` at the upper one where the range
is certified free of poles, the coordinate unbounded otherwise. -/
def Interval.tan (p : ℕ) (I : Interval (Vec 𝕋 n)) : Interval.EBox 𝕋 n where
  lo := fun i =>
    match Interval.step_tanBranch p (I.inf i) (I.sup i) with
    | some true => some (tanDown p (I.inf i))
    | some false => some (tanDownNeg p (I.inf i))
    | none => none
  hi := fun i =>
    match Interval.step_tanBranch p (I.inf i) (I.sup i) with
    | some true => some (tanUp p (I.sup i))
    | some false => some (tanUpNeg p (I.sup i))
    | none => none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
