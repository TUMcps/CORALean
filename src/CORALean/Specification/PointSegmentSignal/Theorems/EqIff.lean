module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic

@[expose] public section

/-!
# Equality of signals over a linear order

At a linear order two time points agree iff they are equal, so `eq` is structural equality of the
signals.

## Inputs
* `T` – time type with a linear order
* `a` – first signal
* `b` – second signal

## Hypotheses
* none

## Conclusion
* `eq` holds iff the signals are equal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Comparing two lists entry by entry with `decide (x = y)` is equality of the lists. -/
private theorem aux_isEqv_decide_iff {α : Type} [DecidableEq α] (as bs : List α) : -- --- CONCL ---
    as.isEqv bs (fun x y => decide (x = y)) = true ↔ as = bs := by -- --- PROOF ---
  induction as generalizing bs with
  | nil => cases bs <;> simp
  | cons a as ih =>
    cases bs with
    | nil => simp
    | cons b bs =>
      simp only [List.isEqv_cons_cons, Bool.and_eq_true, decide_eq_true_eq, ih, List.cons.injEq]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.eq_iff {T : Type} [LinearOrder T] (a b : PointSegmentSignal T) :
    a.eq b = true ↔ a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [PointSegmentSignal.eq, TimeOrder.eqv_iff_eq, Bool.and_eq_true, beq_iff_eq,
    aux_isEqv_decide_iff, PointSegmentSignal.mk.injEq]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
