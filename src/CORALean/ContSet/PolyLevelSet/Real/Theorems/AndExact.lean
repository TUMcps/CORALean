module

public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalAnd
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds

@[expose] public section

/-!
# `PolyLevelSet.and_` is exact

Stacking the rows is intersecting the sets, whatever the operators: the stacked values are the two
operands' side by side (`eval_and_`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stacked rows denote the intersection of the two sets. -/
theorem PolyLevelSet.and_exact (P₁ P₂ : PolyLevelSet n) :
    (P₁.and_ P₂).construct = P₁.construct ∩ P₂.construct := by
  ext x
  show (∀ i, ((P₁.and_ P₂).op i).holds ((P₁.and_ P₂).eval x i)) ↔ _
  rw [PolyLevelSet.eval_and_]
  exact LevelSet.forall_append_holds _ _ _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
