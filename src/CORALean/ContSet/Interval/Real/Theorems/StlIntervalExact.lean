module

public import CORALean.ContSet.Interval.Real.Operations.StlInterval

@[expose] public section

/-!
# `Interval.stlInterval` is exact

The set of times of the STL interval is the set of values of the one coordinate over the box.

## Inputs
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the scalar interval is exactly the image of the one-dimensional box
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.stlInterval_exact (I : Interval (Vec ℝ 1)) : -- --- CONCL ---
    I.stlInterval = (fun x : Vec ℝ 1 => x 0) '' I.construct := by -- --- PROOF ---
  ext t
  constructor
  · intro h
    refine ⟨fun _ => t, fun i => ?_, rfl⟩
    rw [Subsingleton.elim i 0]
    exact h
  · rintro ⟨x, hx, rfl⟩
    exact hx 0


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
