module

public import CORALean.Specification.PointSegmentSignal.Operations.AnyTrue
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.MemTakeDrop
public import CORALean.Specification.PointSegmentSignal.Theorems.RelevantCells
public import CORALean.Specification.PointSegmentSignal.Theorems.AtEqCell

@[expose] public section

/-!
# Whether some value in an interval satisfies a condition

In dense time without a last moment, for a valid signal and a nonempty interval with lower bound `lb
≥ 0`, `anyTrue(obj,interval,cond)` is `true` iff `cond` holds of the signal's value at some time of
the interval.

## Inputs
* `T` – time type
* `s` – signal
* `lb` – interval lower bound
* `ub` – interval upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed
* `cond` – condition on values

## Hypotheses
* `hs` – the signal is valid
* `h0` – the lower bound is nonnegative
* `hne` – the interval is nonempty

## Conclusion
* `anyTrue` holds iff the condition holds at some time of the interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `anyTrue` is true iff `cond` holds of the signal's value at some time of the interval. -/
theorem PointSegmentSignal.anyTrue_spec {T : Type} [LinearOrder T] [Zero T] [DenselyOrdered T]
    [NoMaxOrder T] (s : PointSegmentSignal T) (hs : s.IsValid) (lb : T) (ub : WithTop T)
    (lc rc : Bool) (cond : Bool → Bool) (h0 : 0 ≤ lb)
    (hne : STLInterval.emptyBounds lb ub lc rc = false) : -- --- CONCL ---
    s.anyTrue lb ub lc rc cond = true ↔
      ∃ t : T, STLInterval.IsInBounds lb ub lc rc t ∧ cond (s.at t) = true := by -- --- PROOF ---
  have hget : ∀ m (h : m < s.values.length), s.values[m] = s.values.getD m false := fun m h => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  unfold PointSegmentSignal.anyTrue
  rw [List.any_eq_true]
  constructor
  · -- an entry of the slice is read at some time of the interval
    rintro ⟨x, hx, hc⟩
    obtain ⟨m, hm1, hm2, hm3, rfl⟩ := (List.mem_take_drop_iff _ _ _ _).1 hx
    obtain ⟨t, ht, hct⟩ := (s.relevant_cells hs lb ub lc rc h0 hne m).1 ⟨hm1, hm2, hm3⟩
    refine ⟨t, ht, ?_⟩
    rwa [PointSegmentSignal.at_eq_cell, hct, ← hget m hm3]
  · rintro ⟨t, ht, hc⟩
    obtain ⟨h1, h2, h3⟩ := (s.relevant_cells hs lb ub lc rc h0 hne (s.cell t)).2 ⟨t, ht, rfl⟩
    refine ⟨s.values[s.cell t], (List.mem_take_drop_iff _ _ _ _).2 ⟨s.cell t, h1, h2, h3, rfl⟩, ?_⟩
    rwa [PointSegmentSignal.at_eq_cell, ← hget _ h3] at hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
