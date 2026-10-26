module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.Basic

@[expose] public section

/-!
# Equality of float signals, read as reals

Over a float scalar `𝕋` `eq` compares the time points by the reals they denote (`TimeOrder.Eqv`),
so the signals read as reals compare as the float ones, and a float `true` is equality of the
signals read as reals.

## Inputs
* `a` – first signal
* `b` – second signal

## Hypotheses
* none

## Conclusion
* the comparison of the signals read as reals is the float one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Mapping both lists by `f` maps the entrywise test to the test on the images. -/
private theorem aux_isEqv_map {α β : Type} (f : α → β) (p : β → β → Bool) (as bs : List α) :
    (as.map f).isEqv (bs.map f) p = as.isEqv bs (fun x y => p (f x) (f y)) := by
  induction as generalizing bs with
  | nil => cases bs <;> simp
  | cons a as ih => cases bs <;> simp [List.isEqv, ih]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.eq_mapTime (a b : PointSegmentSignal 𝕋) : -- --- CONCL ---
    (a.mapTime toReal).eq (b.mapTime toReal) = a.eq b := by -- --- PROOF ---
  -- the time points compare as the reals they denote on both sides
  unfold PointSegmentSignal.eq PointSegmentSignal.mapTime
  simp only [aux_isEqv_map]
  have h : (fun x y : 𝕋 => decide (TimeOrder.Eqv (toReal x) (toReal y))) =
      fun x y => decide (TimeOrder.Eqv x y) :=
    funext fun _ => funext fun _ => decide_eq_decide.mpr Iff.rfl
  rw [h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
