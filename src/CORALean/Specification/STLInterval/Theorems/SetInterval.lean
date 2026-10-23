module

public import CORALean.Specification.STLInterval.Operations.Interval
public import CORALean.ContSet.Interval.Real.Theorems.StlIntervalExact
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetBoundsNe
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.DenselyOrdered

@[expose] public section

/-!
# `interval` is the closure of the times

For an interval with a finite upper bound the box `interval(I)` denotes the closure of the set of
times:
both ends closed, the same bounds.

## Inputs
* `l` – lower bound
* `u` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed
* `b` – an infinite upper bound is open
* `c` – the bounds leave a time in the interval
* `z` – the lower bound is nonnegative

## Hypotheses
* none

## Conclusion
* the box of the interval is the closure of its times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic


-- =======================================  MAIN THEOREM  ======================================= --

/-- The box of a bounded STL interval is the closure of its times. -/
theorem STLInterval.set_interval (l u : ℝ) (lc rc : Bool) (b c z) : -- --- CONCL ---
    (fun x : Vec ℝ 1 => x 0) ''
      (STLInterval.nonempty l (u : WithTop ℝ) lc rc b c z).interval.construct =
        closure (STLInterval.nonempty l (u : WithTop ℝ) lc rc b c z).set := by -- --- PROOF ---
  have himg : (fun x : Vec ℝ 1 => x 0) ''
      (STLInterval.nonempty l (u : WithTop ℝ) lc rc b c z).interval.construct = Set.Icc l u :=
    (Real.Interval.stlInterval_exact _).symm
  rw [himg]
  show _ = closure (rawSet (toReal l : ℝ) (toEReal (u : WithTop ℝ)) lc rc)
  simp only [toReal_real, STLInterval.toEReal_coe] at c ⊢
  -- closing an interval with real bounds gives `Icc`, whatever its flags
  rcases c with h | ⟨e, hc, hr⟩
  · have hxy : l < u := EReal.coe_lt_coe_iff.1 h
    cases lc <;> cases rc
    · rw [show rawSet (l : EReal) u false false = Set.Ioo l u by
        ext t; simp [rawSet], closure_Ioo hxy.ne]
    · rw [show rawSet (l : EReal) u false true = Set.Ioc l u by
        ext t; simp [rawSet, le_iff_lt_or_eq, eq_comm], closure_Ioc hxy.ne]
    · rw [show rawSet (l : EReal) u true false = Set.Ico l u by
        ext t; simp [rawSet, le_iff_lt_or_eq, eq_comm], closure_Ico hxy.ne]
    · rw [rawSet_closed_coe, closure_Icc]
  · subst hc hr
    rw [rawSet_closed_coe, closure_Icc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
