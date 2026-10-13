import CORALean.ContSet.Interval.Real.Operations.ContainsScalingCora

/-!
# CORA's `interval/contains_` scaling branch accepts a point outside the interval

For `I = interval(1, 3)` and `S = 0`: `c = 2`, `scaling = abs(0)./abs([-1 1]) = [0 0]`, so
`res = [1 1]` although `0 ∉ [1, 3]`. Reached by `[res,cert,scaling] = contains(I, 0)`
(`contSet/contains.m` l. 87-91). Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every entry of CORA's `res` holds for `S = 0` and `I = [1, 3]`, yet `0 ∉ I`. -/
theorem Interval.containsScalingCora_counterexample :
    ∃ (I : Interval (Vec ℝ 1)) (S : Vec ℝ 1),
      (∀ j, I.containsScalingCora S 0 j) ∧ S ∉ I.construct := by -- --- PROOF ---
  refine ⟨⟨fun _ => 1, fun _ => 3⟩, fun _ => 0, fun j => ?_, fun h => ?_⟩
  · simp [Interval.containsScalingCora]
  · have := (h 0).1
    simp [Entrywise.entry] at this
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
