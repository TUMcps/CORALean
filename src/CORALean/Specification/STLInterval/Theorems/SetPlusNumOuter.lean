module

public import CORALean.Specification.STLInterval.Operations.PlusNum
public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.RawSetMono
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.ToERealMapAddUpGe

@[expose] public section

/-!
# `plusNum` over a float scalar encloses the shift

Over a float scalar `plusNum` rounds the lower bound down and the upper one up, so it denotes every
time of `I` shifted by the real `c` and possibly more: an outward enclosure of `set_plusNum`.

## Inputs
* `I` – interval
* `c` – number

## Hypotheses
* `hc` – the rounded lower bound stays nonnegative

## Conclusion
* the shifted times lie in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.set_plusNum_outer (I : STLInterval 𝕋) (c : 𝕋)
    (hc : I ≠ .empty → 0 ≤ toReal (addDown I.lowerBound c)) : -- --- CONCL ---
    (fun t => t + toReal c) '' I.set ⊆ (I.plusNum c hc).set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.set]
  | nonempty l u lc rc b c' _ =>
    simp only [STLInterval.plusNum]
    rw [set_stlInterval]
    have := rawSet_add (rawSet_nonempty_of_fields b c')
      (rawSet_closed_nonempty (le_refl (toReal c)))
    rw [rawSet_closed_coe, Set.Icc_self, Set.add_singleton] at this
    simp only [Bool.and_true] at this
    show (fun t => t + toReal c) '' rawSet (toReal l : ℝ) (toEReal u) lc rc ⊆ _
    rw [← this]
    refine rawSet_mono ?_ (STLInterval.toEReal_map_addUp_ge u c)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    exact addDown_le_add l c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
