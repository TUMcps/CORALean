module

public import CORALean.Specification.STLInterval.Operations.And
public import CORALean.Specification.STLInterval.Theorems.LowerStlInterval

@[expose] public section

/-!
# The lower bound of an intersection

If the second operand of `and_` has lower bound `≥ 0`, so has the intersection.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The intersection has lower bound `≥ 0` if the second operand has. -/
theorem STLInterval.fields_and_right (I J : STLInterval)
    (hJ : ∀ f, J.fieldsOf = some f → 0 ≤ f.lower) :
    ∀ f, (I.and_ J).fieldsOf = some f → 0 ≤ f.lower := by -- --- PROOF ---
  intro f hf
  cases I with
  | empty => simp [STLInterval.and_, STLInterval.fieldsOf] at hf
  | nonempty l₁ u₁ lc₁ rc₁ a₁ b₁ c₁ =>
    cases J with
    | empty => simp [STLInterval.and_, STLInterval.fieldsOf] at hf
    | nonempty l₂ u₂ lc₂ rc₂ a₂ b₂ c₂ =>
      -- the lower bound is the larger of the two
      simp only [STLInterval.and_] at hf
      rw [STLInterval.lower_stlInterval _ _ _ _ f hf]
      exact (hJ _ rfl).trans (le_max_right _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
