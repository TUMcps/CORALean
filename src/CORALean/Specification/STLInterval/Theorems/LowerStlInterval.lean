module

public import CORALean.Specification.STLInterval.Definitions.Fields
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# The lower bound `stlInterval(lb,ub,lc,rc)` keeps

The constructor either gives the empty interval or an interval with lower bound `lb`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A nonempty `stlInterval(lb,ub,lc,rc)` has lower bound `lb`. -/
theorem STLInterval.lower_stlInterval (lb ub : EReal) (lc rc : Bool) :
    ∀ f, (STLInterval.stlInterval lb ub lc rc).fieldsOf = some f →
      f.lower = lb := by -- --- PROOF ---
  intro f hf
  -- every case of the constructor either is empty or keeps the lower bound
  unfold STLInterval.stlInterval at hf
  dsimp only at hf
  split_ifs at hf <;> simp_all [STLInterval.fieldsOf] <;> rw [← hf]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
