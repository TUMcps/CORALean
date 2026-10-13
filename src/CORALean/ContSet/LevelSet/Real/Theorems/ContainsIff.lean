module

public import CORALean.ContSet.LevelSet.Real.Operations.Contains

@[expose] public section

/-!
# `LevelSet.contains` decides membership

The boolean answer is `true` exactly when the point is in the denoted set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.contains_iff (L : LevelSet n) (x : Vec ℝ n) :
    L.contains x = true ↔ x ∈ L.construct := by -- --- PROOF ---
  have key : ∀ (c : CompOp) (v : ℝ), c.test v = true ↔ c.holds v := by
    intro c v
    cases c <;> simp [CompOp.test, CompOp.holds]
  simp only [LevelSet.contains, List.all_eq_true, List.mem_finRange, true_implies, key]
  exact Iff.rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
