module

public import CORALean.Specification.STLInterval.Operations.PlusNum
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# `plus` with a number denotes a shift

`I + c` denotes `I` shifted by `c`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- `plusNum` denotes `I` shifted by `c`. -/
theorem STLInterval.set_plusNum (I : STLInterval) (c : ℝ) :
    (I.plusNum c).set = (fun t => t + c) '' I.set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.plusNum, STLInterval.set]
  | nonempty l u lc rc a b c' =>
    simp only [STLInterval.plusNum]
    rw [set_stlInterval, ← Set.add_singleton, ← Set.Icc_self c, ← rawSet_closed_coe]
    have := rawSet_add (set_nonempty _ _ _ _ a b c') (rawSet_closed_nonempty (le_refl c))
    simpa [STLInterval.set] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
