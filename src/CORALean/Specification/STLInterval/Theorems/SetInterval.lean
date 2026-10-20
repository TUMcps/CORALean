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

For an interval with finite bounds the box `interval(I)` denotes the closure of the set of times:
both ends closed, the same bounds.

## Inputs
* `l` – lower bound
* `u` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed
* `a` – an infinite lower bound is open
* `b` – an infinite upper bound is open
* `c` – the bounds leave a time in the interval
* `z` – the lower bound is nonnegative

## Hypotheses
* `hl` – the lower bound is finite
* `hu` – the upper bound is finite

## Conclusion
* the box of the interval is the closure of its times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The box of a bounded STL interval is the closure of its times. -/
theorem STLInterval.set_interval (l u : EReal) (lc rc : Bool) (a b c z) (hl : l ≠ ⊥) (hu : u ≠ ⊤) :
    (fun x : Vec ℝ 1 => x 0) ''
      (STLInterval.nonempty l u lc rc a b c z).interval.construct =
        closure (STLInterval.nonempty l u lc rc a b c z).set := by -- --- PROOF ---
  have hne := rawSet_nonempty_of _ _ _ _ a b c
  have hlt := (rawSet_bounds_ne hne).1
  have hub := (rawSet_bounds_ne hne).2
  -- the bounds are real: name them
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, l = x := ⟨l.toReal, (EReal.coe_toReal hlt hl).symm⟩
  obtain ⟨y, rfl⟩ : ∃ y : ℝ, u = y := ⟨u.toReal, (EReal.coe_toReal hu hub).symm⟩
  have himg : (fun x : Vec ℝ 1 => x 0) ''
      (STLInterval.nonempty (x : EReal) y lc rc a b c z).interval.construct = Set.Icc x y :=
    (Real.Interval.stlInterval_exact _).symm
  rw [himg]
  show _ = closure (rawSet x y lc rc)
  -- closing an interval with real bounds gives `Icc`, whatever its flags
  rcases c with h | ⟨e, hc, hr⟩
  · have hxy : x < y := EReal.coe_lt_coe_iff.1 h
    cases lc <;> cases rc
    · rw [show rawSet (x : EReal) y false false = Set.Ioo x y by
        ext t; simp [rawSet], closure_Ioo hxy.ne]
    · rw [show rawSet (x : EReal) y false true = Set.Ioc x y by
        ext t; simp [rawSet, le_iff_lt_or_eq, eq_comm], closure_Ioc hxy.ne]
    · rw [show rawSet (x : EReal) y true false = Set.Ico x y by
        ext t; simp [rawSet, le_iff_lt_or_eq, eq_comm], closure_Ico hxy.ne]
    · rw [rawSet_closed_coe, closure_Icc]
  · subst hc hr
    rw [rawSet_closed_coe, closure_Icc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
