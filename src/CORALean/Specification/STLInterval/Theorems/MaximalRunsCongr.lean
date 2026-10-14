module

public import CORALean.Specification.STLInterval.Definitions.MaximalRuns

@[expose] public section

/-!
# Maximal runs depend on a property only at times `≥ 0`

Two properties that agree at all times `t ≥ 0` have the same maximal runs.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- Properties that agree at times `≥ 0` have the same maximal runs. -/
theorem STLInterval.maximalRuns_congr (L : List STLInterval) (P Q : ℝ → Prop)
    (h : ∀ t : ℝ, 0 ≤ t → (P t ↔ Q t)) :
    STLInterval.MaximalRuns L P ↔ STLInterval.MaximalRuns L Q := by -- --- PROOF ---
  unfold STLInterval.MaximalRuns
  refine and_congr Iff.rfl (and_congr (forall_congr' fun t => forall_congr' fun ht => ?_)
    (forall_congr' fun I => forall_congr' fun hI => forall_congr' fun t₁ =>
      forall_congr' fun h₁ => forall_congr' fun t₂ => forall_congr' fun ht₂ => ?_))
  · exact iff_congr Iff.rfl (h t ht)
  · -- the path condition, at times `≥ 0`
    exact imp_congr_left (forall_congr' fun t => forall_congr' fun ht =>
      forall_congr' fun _ => forall_congr' fun _ => h t ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
