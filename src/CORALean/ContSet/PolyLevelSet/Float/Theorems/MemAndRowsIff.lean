module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.Basic
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.EvalNominalCoreAnd
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalAnd

@[expose] public section

/-!
# A point of `PolyLevelSet.andRows`, over a floating-point scalar

A point of `P.andRows Q` is a point of `P`, its box included, at which `Q`'s rows hold within their
slacks as well; `Q`'s box is not read. The read-back rows are the exact layer's stacked rows
(`eval_nominalCore_and_`), so this is `Real.PolyLevelSet.mem_andRows_iff` with slacks.

## Inputs
* `P` – level set
* `Q` – level set whose rows are added
* `x` – real point

## Hypotheses
* none

## Conclusion
* `x` lies in `P.andRows Q` iff it lies in `P` and meets `Q`'s rows
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of `P.andRows Q` is a point of `P` at which `Q`'s rows hold within their slacks. -/
theorem PolyLevelSet.mem_andRows_iff (P Q : PolyLevelSet 𝕋 n) (x : Vec ℝ n) : -- --- CONCL ---
    x ∈ (P.andRows Q).construct ↔ x ∈ P.construct
      ∧ ∀ i, (Q.op i).IsMetWithin (Q.nominalCore.eval x i)
        |toReal (Q.b_error i)| := by -- --- PROOF ---
  show (x ∈ P.dom.construct ∧ ∀ i : Fin (P.m + Q.m), ((P.and_ Q).op i).IsMetWithin
    ((P.and_ Q).nominalCore.eval x i) |toReal ((P.and_ Q).b_error i)|) ↔ _
  rw [PolyLevelSet.eval_nominalCore_and_, Real.PolyLevelSet.eval_and_, Real.LevelSet.forall_fin_add]
  simp only [PolyLevelSet.and_, Fin.append_left, Fin.append_right]
  exact ⟨fun ⟨h, r₁, r₂⟩ => ⟨⟨h, r₁⟩, r₂⟩, fun ⟨⟨h, r₁⟩, r₂⟩ => ⟨h, r₁, r₂⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
