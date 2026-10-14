module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Capsule.Real.Theorems.ConstructSubsetOfDistLe
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Capsule
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# A box as a capsule, over a floating-point scalar — the construction

`Interval.capsuleAlong`, `Interval.widestAxis` and `Interval.capsule` are the constructions;
`Interval_to_Capsule` states and proves what they guarantee.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
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
  let cGap := fun i => subUp (half (addUp (I.inf i) (I.sup i))) (c i)
  let gGap := fun i =>
    if i = a then subUp (half (subUp (I.sup i) (I.inf i))) (half (subDown (I.sup i) (I.inf i)))
    else zero
  let hw := fun i => if i = a then zero else half (subUp (I.sup i) (I.inf i))
  ⟨c, g, addUp (addUp (normUp k hw) (normUp k cGap)) (normUp k gGap)⟩

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
  | none => ⟨fun _ => zero, fun _ => zero, zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
