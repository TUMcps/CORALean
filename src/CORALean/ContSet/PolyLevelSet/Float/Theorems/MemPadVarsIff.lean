module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.PadVars
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalPadVars

@[expose] public section

/-!
# What `PolyLevelSet.padVars` denotes over a floating-point scalar

The set times the whole space of the fresh variables: the padded rows read back as the exact
padded rows, which ignore them (`Real.PolyLevelSet.eval_padVars`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point is in the padded set exactly when its first `n` variables are in the set. -/
theorem PolyLevelSet.mem_padVars_iff (P : PolyLevelSet 𝕋 n) (r : ℕ) (x : Vec ℝ (n + r)) :
    x ∈ (P.padVars r).construct ↔ (fun k => x (Fin.castAdd r k)) ∈ P.construct := by
  show (∀ i, (P.op i).IsMetWithin (P.nominalCore.padVars r |>.eval x i) _) ↔ _
  rw [Real.PolyLevelSet.eval_padVars]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
