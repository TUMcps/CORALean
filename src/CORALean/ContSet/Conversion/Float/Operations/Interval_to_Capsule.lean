module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Capsule.Real.Theorems.ConstructSubsetOfDistLe
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Capsule
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# A box as a capsule, over a floating-point scalar

CORA's `capsule(interval)`: the segment along the widest axis, through the box's center, and a ball
over the half-widths of the other axes. The center and the generator are halves of directed sums
and differences; what they miss of the exact ones goes into the error box (the center's between
`0` and the gap to the upward rounding, the generator's at every segment parameter as the symmetric
box of its gap), and the radius is the half-widths' norm rounded up.

## Inputs
* `k` – Newton steps for the norm
* `I` – interval
* `a` – axis of the segment

## Output
* capsule with its segment along axis `a`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The capsule with the segment along axis `a`. -/
def Interval.capsuleAlong (k : ℕ) (I : Interval (Vec 𝕋 n)) (a : Fin n) : Capsule 𝕋 n :=
  let c := fun i => half (addDown (I.inf i) (I.sup i))
  let g := fun i => if i = a then half (subDown (I.sup i) (I.inf i)) else zero
  let gGap := fun i =>
    if i = a then subUp (half (subUp (I.sup i) (I.inf i))) (half (subDown (I.sup i) (I.inf i)))
    else zero
  let hw := fun i => if i = a then zero else half (subUp (I.sup i) (I.inf i))
  ⟨c, g, normUp k hw, (Interval.residual c (fun i => half (addUp (I.inf i) (I.sup i))) c).plus
    (Interval.symmetric gGap)⟩

/-- The first axis of maximal width, the widths rounded up. `none` exactly when `n = 0`. -/
def Interval.widestAxis (I : Interval (Vec 𝕋 n)) : Option (Fin n) :=
  (List.finRange n).foldl
    (fun best i =>
      match best with
      | none => some i
      | some b =>
        if le (subUp (I.sup i) (I.inf i)) (subUp (I.sup b) (I.inf b)) then some b else some i)
    none

/-- CORA's `capsule(interval)`. -/
def Interval.capsule (k : ℕ) (I : Interval (Vec 𝕋 n)) : Capsule 𝕋 n :=
  match I.widestAxis with
  | some a => I.capsuleAlong k a
  | none => ⟨fun _ => zero, fun _ => zero, zero, Interval.origin n⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
