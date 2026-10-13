module

public import CORALean.ContSet.Interval.Real.Operations.Minus
public import CORALean.ContSet.Interval.Real.Operations.Uminus
public import CORALean.ContSet.Interval.Real.Operations.Plus

@[expose] public section

/-!
# `Interval.minus` is `plus` of the negation

`[a, b] - [c, d]` and `[a, b] + (-[c, d])` have the same bounds, `a - d` being `a + -d`. Equal as
boxes, not merely as sets, so both `minus_outer` and `minus_exact` reduce to `plus`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] [Entrywise α ι] in
theorem Interval.minus_eq_plus_uminus (I₁ I₂ : Interval α) :
    I₁.minus I₂ = I₁.plus I₂.uminus := by
  simp only [Interval.minus, Interval.plus, Interval.uminus, sub_eq_add_neg]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
