module

public import CORALean.ContSet.Interval.Float.Operations.IntersectionExact
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.EvalNominalCoreAnd
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalAnd
public import CORALean.ContSet.LevelSet.Real.Theorems.Basic

@[expose] public section

/-!
# `PolyLevelSet.and_` over a floating-point scalar is exact

Stacking the rows is intersecting the sets: the stack reads back as the exact stack
(`eval_nominalCore_and_`), whose values are the operands' side by side
(`Real.PolyLevelSet.eval_and_`),
and the slacks are stacked alike.

## Inputs
* `P₁` – first level set
* `P₂` – second level set

## Hypotheses
* none

## Conclusion
* `and_` denotes the intersection exactly
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stacked rows on the boxes' intersection denote the intersection of the two sets. -/
theorem PolyLevelSet.and_exact (P₁ P₂ : PolyLevelSet 𝕋 n) : -- --- CONCL ---
    (P₁.and_ P₂).construct = P₁.construct ∩ P₂.construct := by -- --- PROOF ---
  ext x
  show (x ∈ (P₁.dom.intersection P₂.dom).construct ∧ ∀ i : Fin (P₁.m + P₂.m),
    ((P₁.and_ P₂).op i).IsMetWithin ((P₁.and_ P₂).nominalCore.eval x i)
      |toReal ((P₁.and_ P₂).b_error i)|) ↔ _
  rw [PolyLevelSet.eval_nominalCore_and_, Real.PolyLevelSet.eval_and_, Real.LevelSet.forall_fin_add,
    Interval.intersection_exact, Set.mem_inter_iff]
  simp only [PolyLevelSet.and_, Fin.append_left, Fin.append_right]
  exact ⟨fun ⟨⟨h₁, h₂⟩, r₁, r₂⟩ => ⟨⟨h₁, r₁⟩, h₂, r₂⟩, fun ⟨⟨h₁, r₁⟩, h₂, r₂⟩ => ⟨⟨h₁, h₂⟩, r₁, r₂⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
