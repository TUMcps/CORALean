module

public import CORALean.Specification.FourValuedSignal.Definitions.IsValid
public import CORALean.Specification.FourValuedSignal.Operations.FindIntervals
public import CORALean.Specification.STLInterval.Theorems.MaximalRunsCongr
public import CORALean.Specification.FourValuedSignal.Theorems.Basic
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalAtIff
public import CORALean.Specification.KleeneSignal.Theorems.FindIntervalsSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsSpec

@[expose] public section

/-!
# `findIntervals` of a four-valued signal returns the maximal intervals of a value

For a valid four-valued signal, the intervals of `findIntervals(obj,match)` start at times `≥ 0`, a
time `t ≥ 0` is in one of them exactly when the signal is `match` at `t`, and an interval cannot be
extended through times where the signal is `match`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intervals of `findIntervals` are the maximal intervals where the signal is `match`. -/
theorem FourValuedSignal.findIntervals_spec (s : FourValuedSignal ℝ) (hs : s.IsValid)
    (match_ : FourValued) :
    STLInterval.MaximalRuns (s.findIntervals match_)
      (fun t => s.at t = match_) := by -- --- PROOF ---
  -- the Kleene refinements are valid
  have hvf := (s.toKleeneSignal_spec hs Kleene.ff).1
  have hvt := (s.toKleeneSignal_spec hs Kleene.tt).1
  cases match_ with
  | ii =>
    -- the inconclusive intervals are those of `isInconclusive`
    have e : s.findIntervals FourValued.ii = s.isInconclusive.findIntervals := rfl
    rw [e]
    refine (STLInterval.maximalRuns_congr _ _ _ fun t _ => ?_).1
      (s.isInconclusive.findIntervals_spec hs.2 id)
    rw [FourValuedSignal.at_eq_ii_iff]
    rfl
  -- the true intervals are those of the refinement with inconclusive as `False`
  | tt =>
    have e : s.findIntervals FourValued.tt = (s.toKleeneSignal Kleene.ff).findIntervals Kleene.tt :=
      rfl
    rw [e]
    exact (STLInterval.maximalRuns_congr _ _ _ fun t ht =>
      (s.toKleeneSignal_at_iff hs t ht).1).1
      ((s.toKleeneSignal Kleene.ff).findIntervals_spec hvf Kleene.tt)
  -- the false intervals are those of the refinement with inconclusive as `True`
  | ff =>
    have e : s.findIntervals FourValued.ff = (s.toKleeneSignal Kleene.tt).findIntervals Kleene.ff :=
      rfl
    rw [e]
    exact (STLInterval.maximalRuns_congr _ _ _ fun t ht =>
      (s.toKleeneSignal_at_iff hs t ht).2.2.2.2.1).1
      ((s.toKleeneSignal Kleene.tt).findIntervals_spec hvt Kleene.ff)
  -- so are the unknown ones
  | uu =>
    have e : s.findIntervals FourValued.uu = (s.toKleeneSignal Kleene.tt).findIntervals Kleene.uu :=
      rfl
    rw [e]
    exact (STLInterval.maximalRuns_congr _ _ _ fun t ht =>
      (s.toKleeneSignal_at_iff hs t ht).2.2.2.2.2).1
      ((s.toKleeneSignal Kleene.tt).findIntervals_spec hvt Kleene.uu)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
