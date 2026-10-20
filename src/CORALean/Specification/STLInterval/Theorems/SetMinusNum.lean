module

public import CORALean.Specification.STLInterval.Operations.MinusNum
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetSub
public import CORALean.Specification.STLInterval.Theorems.RawSetClamp
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# `minus` with a number denotes a shift down

`I - c` denotes `I` shifted down by `c`, at least `0`.

## Inputs
* `I` – interval
* `c` – number

## Hypotheses
* none

## Conclusion
* the difference denotes the nonnegative shift down by the number
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- `minusNum` denotes `I` shifted down by `c`, at least `0`. -/
theorem STLInterval.set_minusNum (I : STLInterval) (c : ℝ) : -- --- CONCL ---
    (I.minusNum c).set = ((fun t => t - c) '' I.set) ∩ Set.Ici 0 := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.minusNum, STLInterval.set]
  | nonempty l u lc rc a b c' _ =>
    simp only [STLInterval.minusNum]
    have := rawSet_sub (rawSet_nonempty_of _ _ _ _ a b c') (rawSet_closed_nonempty (le_refl c))
    rw [rawSet_closed_coe, Set.Icc_self, Set.sub_singleton] at this
    simp only [Bool.and_true] at this
    show _ = (fun t => t - c) '' rawSet l u lc rc ∩ Set.Ici 0
    rw [← this, rawSet_clamp]
    split_ifs <;> exact set_stlInterval _ _ _ _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
