module

public import CORALean.Specification.STLInterval.Operations.PlusInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetAdd
public import CORALean.Specification.STLInterval.Theorems.RawSetMono
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.ToERealMapAddUpGe

@[expose] public section

/-!
# `plusInterval` over a float scalar encloses the sum

Over a float scalar `plusInterval` rounds the lower bound down and the upper one up, so it denotes
every sum of a time of `I` and one of `[inf, sup]` and possibly more: an outward enclosure of
`set_plusInterval`.

## Inputs
* `I` – interval
* `J` – interval of stored bounds

## Hypotheses
* `hc` – the rounded lower bound stays nonnegative

## Conclusion
* the sums lie in the result
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

theorem STLInterval.set_plusInterval_outer (I : STLInterval 𝕋) (J : Real.Interval (Vec 𝕋 1))
    (hc : I ≠ .empty → ¬ toReal (J.sup 0) < toReal (J.inf 0) →
      0 ≤ toReal (addDown I.lowerBound (J.inf 0))) : -- --- CONCL ---
    I.set + Set.Icc (toReal (J.inf 0)) (toReal (J.sup 0)) ⊆
      (I.plusInterval J hc).set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.set]
  | nonempty l u lc rc b c _ =>
    simp only [STLInterval.plusInterval]
    by_cases h : toReal (J.sup 0) < toReal (J.inf 0)
    · rw [Set.Icc_eq_empty_of_lt h, Set.add_empty]
      exact Set.empty_subset _
    · rw [dif_neg h, set_stlInterval, ← rawSet_closed_coe]
      have := rawSet_add (rawSet_nonempty_of_fields b c) (rawSet_closed_nonempty (not_lt.1 h))
      simp only [Bool.and_true] at this
      show rawSet (toReal l : ℝ) (toEReal u) lc rc + _ ⊆ _
      rw [← this]
      refine rawSet_mono ?_ (STLInterval.toEReal_map_addUp_ge u (J.sup 0))
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      exact addDown_le_add l (J.inf 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
