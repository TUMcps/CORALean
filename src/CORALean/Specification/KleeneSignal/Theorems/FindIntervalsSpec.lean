module

public import CORALean.Specification.KleeneSignal.Definitions.IsValid
public import CORALean.Specification.KleeneSignal.Operations.FindIntervals
public import CORALean.Specification.STLInterval.Theorems.MaximalRunsCongr
public import CORALean.Specification.KleeneSignal.Theorems.Basic
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsSpec

@[expose] public section

/-!
# `findIntervals` of a three-valued signal returns the maximal intervals of a value

For a valid three-valued signal, the intervals of `findIntervals(obj,match)` start at times `≥ 0`, a
time `t ≥ 0` is in one of them exactly when the signal is `match` at `t`, and an interval cannot be
extended through times where the signal is `match`.

## Inputs
* `s` – three-valued signal
* `match_` – value to find

## Hypotheses
* `hs` – the signal is valid

## Conclusion
* the intervals are the maximal runs of that value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intervals of `findIntervals` are the maximal intervals where the signal is `match`. -/
theorem KleeneSignal.findIntervals_spec (s : KleeneSignal ℝ) (hs : s.IsValid)
    (match_ : Kleene) : -- --- CONCL ---
    STLInterval.IsMaximalRuns (s.findIntervals match_)
      (fun t => s.at t = match_) := by -- --- PROOF ---
  cases match_ with
  | uu =>
    -- the unknown intervals are those of `isUnknown`
    have e : s.findIntervals Kleene.uu = s.isUnknown.findIntervals := rfl
    rw [e]
    refine (STLInterval.maximalRuns_congr _ _ _ fun t _ => ?_).1
      (s.isUnknown.findIntervals_spec hs.2 id)
    rw [KleeneSignal.at_eq_uu_iff]
    rfl
  | tt =>
    -- the true intervals are those of the Boolean signal with unknown mapped to false
    obtain ⟨hv, hb⟩ := KleeneSignal.toBoolSignal_spec s hs false
    have e : s.findIntervals Kleene.tt = (s.toBoolSignal false).findIntervals := rfl
    rw [e]
    refine (STLInterval.maximalRuns_congr _ _ _ fun t ht => ?_).1
      ((s.toBoolSignal false).findIntervals_spec hv id)
    obtain ⟨h1, h2⟩ := hb t ht
    by_cases hu : s.at t = Kleene.uu
    · exact iff_of_false (by rw [id, h1 hu]; exact Bool.false_ne_true)
        (by rw [hu]; exact Kleene.noConfusion)
    · show id _ = true ↔ _
      rw [id, h2 hu]
      generalize s.at t = k
      cases k <;> simp [Kleene.toBool]
  | ff =>
    -- the false intervals are those of the negated Boolean signal with unknown mapped to true
    obtain ⟨hv, hb⟩ := KleeneSignal.toBoolSignal_spec s hs true
    have e : s.findIntervals Kleene.ff = (s.toBoolSignal true).findIntervals (fun x => !x) := rfl
    rw [e]
    refine (STLInterval.maximalRuns_congr _ _ _ fun t ht => ?_).1
      ((s.toBoolSignal true).findIntervals_spec hv (fun x => !x))
    obtain ⟨h1, h2⟩ := hb t ht
    by_cases hu : s.at t = Kleene.uu
    · exact iff_of_false (by show ¬ (!_) = true; rw [h1 hu]; exact Bool.false_ne_true)
        (by rw [hu]; exact Kleene.noConfusion)
    · show (!_) = true ↔ _
      rw [h2 hu]
      generalize s.at t = k at hu ⊢
      cases k <;> first | exact absurd rfl hu | simp [Kleene.toBool]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
