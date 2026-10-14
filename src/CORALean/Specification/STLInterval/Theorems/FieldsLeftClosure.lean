module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.LowerStlInterval

@[expose] public section

/-!
# The lower bound of a left closure

The left closure of an interval with lower bound `≥ 0` has lower bound `≥ 0`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `leftClosure` keeps a lower bound `≥ 0`. -/
theorem STLInterval.fields_leftClosure (I : STLInterval)
    (hI : ∀ f, I.fieldsOf = some f → 0 ≤ f.lower) :
    ∀ f, I.leftClosure.fieldsOf = some f → 0 ≤ f.lower := by -- --- PROOF ---
  intro f hf
  cases I with
  | empty => simp [STLInterval.leftClosure, STLInterval.fieldsOf] at hf
  | nonempty l u lc rc a b c =>
    by_cases hl : l = ⊥
    · exact absurd (hI _ rfl) (by simp [hl])
    · -- the left end is made closed
      simp only [STLInterval.leftClosure, hl, if_false] at hf
      rw [STLInterval.lower_stlInterval _ _ _ _ f hf]
      exact hI _ rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
