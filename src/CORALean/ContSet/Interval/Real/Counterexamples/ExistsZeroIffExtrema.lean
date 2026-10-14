module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Set.Defs

@[expose] public section

/-!
# Without continuity, `0 ∈ [h̲, h̅]` is not sufficient

[1, Sec. 3 (extremal functions)] calls `0 ∈ [h̲(x), h̅(x)]` necessary and sufficient for
`f(x, y) = 0` to have a solution `y ∈ [Y]`. For `f(x, y) = -1` at `y ≤ 0` and `1` at `y > 0`
on `[Y] = [-1, 1]`, the minimum `-1` and the maximum `1` bracket `0`, and `f` never vanishes.
`Interval.exists_zero_iff_extrema` restores the equivalence for continuous `f(x, ·)`.

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". In Proc. of the 16th International Conference on Principles
      and Practice of Constraint Programming (CP 2010), LNCS 6308, pp. 491-498, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.exists_zero_iff_extrema_counterexample :
    let g : ℝ → ℝ := fun y => if y ≤ 0 then -1 else 1
    IsLeast (g '' Set.Icc (-1) 1) (-1) ∧ IsGreatest (g '' Set.Icc (-1) 1) 1 ∧
      (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 ∧ ¬ ∃ y ∈ Set.Icc (-1 : ℝ) 1, g y = 0 := by -- --- PROOF ---
  intro g
  -- every value of `g` is `-1` or `1`, both taken on `[-1, 1]`
  have hval : ∀ y, g y = -1 ∨ g y = 1 := fun y => by
    by_cases h : y ≤ 0
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  refine ⟨⟨⟨-1, ⟨le_rfl, by norm_num⟩, if_pos (by norm_num)⟩, ?_⟩,
    ⟨⟨1, ⟨by norm_num, le_rfl⟩, if_neg (by norm_num)⟩, ?_⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    rcases hval y with h | h <;> norm_num [h]
  · rintro _ ⟨y, _, rfl⟩
    rcases hval y with h | h <;> norm_num [h]
  · rintro ⟨y, _, hy⟩
    rcases hval y with h | h <;> rw [h] at hy <;> norm_num at hy

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
