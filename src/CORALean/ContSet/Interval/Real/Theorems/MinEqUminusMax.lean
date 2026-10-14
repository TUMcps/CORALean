module

public import CORALean.ContSet.Interval.Real.Operations.Min
public import CORALean.ContSet.Interval.Real.Operations.Max
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.min` is `-max(-I, -J)`

CORA's definition of `min`, `-max(-I, -Y)`, agrees with the coordinatewise smaller bounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.min_eq_uminus_max (I₁ I₂ : Interval α) :
    I₁.min I₂ = (I₁.uminus.max I₂.uminus).uminus := by
  have e : ∀ a b : ℝ, Min.min a b = -Max.max (-a) (-b) := fun a b => by
    rw [← min_neg_neg, neg_neg, neg_neg]
  unfold Interval.min Interval.max Interval.uminus
  congr 1 <;> refine Entrywise.ext fun i => ?_ <;> simp [Entrywise.entry_neg, e]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
