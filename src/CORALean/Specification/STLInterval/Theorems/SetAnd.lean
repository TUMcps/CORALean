module

public import CORALean.Specification.STLInterval.Operations.And
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetInter

@[expose] public section

/-!
# `and_` denotes the intersection

`I & J` denotes the intersection of the two sets of times.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `and_` denotes the intersection of the two sets. -/
theorem STLInterval.set_and_ (I J : STLInterval) :
    (I.and_ J).set = I.set ∩ J.set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.and_, STLInterval.set]
  | nonempty l₁ u₁ lc₁ rc₁ _ _ _ _ =>
    cases J with
    | empty => simp [STLInterval.and_, STLInterval.set]
    | nonempty l₂ u₂ lc₂ rc₂ _ _ _ _ =>
      simp only [STLInterval.and_]
      rw [STLInterval.set_stlInterval]
      exact (rawSet_inter l₁ u₁ l₂ u₂ lc₁ rc₁ lc₂ rc₂).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
