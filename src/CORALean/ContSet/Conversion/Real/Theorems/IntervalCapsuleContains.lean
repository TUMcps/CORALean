module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Capsule
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalCapsuleAlongContains

@[expose] public section

/-!
# A box as a capsule

`Interval.capsule_contains`: its `capsule` contains it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.capsule_contains (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.capsule.construct := by -- --- PROOF ---
  unfold Interval.capsule
  cases h : (List.finRange n).argmax (fun i => I.sup i - I.inf i) with
  | some k => exact I.capsuleAlong_contains k
  | none =>
    have hn : List.finRange n = [] := List.argmax_eq_none.mp h
    obtain rfl : n = 0 := by simpa [List.finRange_eq_nil_iff] using hn
    intro x _
    exact ⟨0, by simp, by simp⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
