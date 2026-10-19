module

public import CORALean.ContSet.PolyLevelSet.Float.Theorems.EvalNominalCoreRelax

@[expose] public section

/-!
# What `PolyLevelSet.relax` denotes over a floating-point scalar

With every row an equation, the rows with their slacks moved into variables are the exact rows
relaxed by the slacks (`eval_nominalCore_relax`): the slack left is `zero`, so each row is met
exactly.
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

/-- The slack-free relaxed rows denote the exact relaxation by the read-back slack. -/
theorem PolyLevelSet.mem_relax_iff {P : PolyLevelSet 𝕋 n} (h : ∀ i, P.op i = .eq)
    (x : Vec ℝ (n + P.m)) :
    x ∈ P.relax.construct
      ↔ x ∈ (P.nominalCore.relax (toRealVec P.b_error)).construct := by -- --- PROOF ---
  refine forall_congr' fun i => ?_
  show (P.op i).IsMetWithin (P.relax.nominalCore.eval x i) |toReal (zero : 𝕋)|
    ↔ (P.op i).holds ((P.nominalCore.relax (toRealVec P.b_error)).eval x i)
  rw [PolyLevelSet.eval_nominalCore_relax, h i, toReal_zero, abs_zero]
  exact abs_nonpos_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
