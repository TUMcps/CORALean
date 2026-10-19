module

public import CORALean.ContSet.Interval.Real.Operations.IntersectionExact
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalAnd
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds

@[expose] public section

/-!
# `PolyLevelSet.and_` is exact

Stacking the rows is intersecting the sets, whatever the operators: the stacked values are the two
operands' side by side (`eval_and_`).

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

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stacked rows on the boxes' intersection denote the intersection of the two sets. -/
theorem PolyLevelSet.and_exact (P₁ P₂ : PolyLevelSet n) :
    (P₁.and_ P₂).construct = P₁.construct ∩ P₂.construct := by -- --- PROOF ---
  ext x
  show (x ∈ (P₁.dom.intersection P₂.dom).construct
    ∧ ∀ i, ((P₁.and_ P₂).op i).holds ((P₁.and_ P₂).eval x i)) ↔ _
  rw [PolyLevelSet.eval_and_, Interval.intersection_exact]
  show (_ ∧ ∀ i, (Fin.append P₁.op P₂.op i).holds _) ↔ _
  rw [LevelSet.forall_append_holds, Set.mem_inter_iff]
  exact ⟨fun ⟨⟨h₁, h₂⟩, r₁, r₂⟩ => ⟨⟨h₁, r₁⟩, h₂, r₂⟩, fun ⟨⟨h₁, r₁⟩, h₂, r₂⟩ => ⟨⟨h₁, h₂⟩, r₁, r₂⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
