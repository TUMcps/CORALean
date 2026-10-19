module

public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalPadVars

@[expose] public section

/-!
# What `PolyLevelSet.padVars` denotes

The set times the whole space of the fresh variables: no row reads them (`eval_padVars`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point is in the padded set exactly when its first `n` variables are in the set. -/
theorem PolyLevelSet.mem_padVars_iff (P : PolyLevelSet n) (r : ℕ) (x : Vec ℝ (n + r)) :
    x ∈ (P.padVars r).construct ↔ (fun k => x (Fin.castAdd r k)) ∈ P.construct := by
  show (∀ i, (P.op i).holds ((P.padVars r).eval x i)) ↔ _
  rw [PolyLevelSet.eval_padVars]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
