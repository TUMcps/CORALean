module

public import CORALean.Specification.STLInterval.Operations.MinusInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetClampMono
public import CORALean.Specification.STLInterval.Theorems.RawSetMono
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.RawSetSub
public import CORALean.Specification.STLInterval.Theorems.SetClamp
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.ToERealMapSubUpGe

@[expose] public section

/-!
# `minusInterval` over a float scalar encloses the difference

Over a float scalar `minusInterval` rounds the lower bound down and the upper one up before the cut
at `0`, so it denotes every difference `≥ 0` of a time of `I` and one of `[inf, sup]`, and possibly
more: an outward enclosure of `set_minusInterval`.

## Inputs
* `I` – interval
* `J` – interval of stored bounds

## Hypotheses
* none

## Conclusion
* the differences `≥ 0` lie in the result
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

theorem STLInterval.set_minusInterval_outer (I : STLInterval 𝕋)
    (J : Real.Interval (Vec 𝕋 1)) : -- --- CONCL ---
    (I.set - Set.Icc (toReal (J.inf 0)) (toReal (J.sup 0))) ∩ Set.Ici 0 ⊆
      (I.minusInterval J).set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.set]
  | nonempty l u lc rc b c _ =>
    simp only [STLInterval.minusInterval]
    by_cases h : toReal (J.sup 0) < toReal (J.inf 0)
    · rw [Set.Icc_eq_empty_of_lt h, Set.sub_empty, Set.empty_inter]
      exact Set.empty_subset _
    · rw [if_neg h, STLInterval.set_clamp]
      have := rawSet_sub (rawSet_nonempty_of_fields b c) (rawSet_closed_nonempty (not_lt.1 h))
      rw [rawSet_closed_coe] at this
      simp only [Bool.and_true] at this
      show (rawSet (toReal l : ℝ) (toEReal u) lc rc - _) ∩ Set.Ici 0 ⊆ _
      rw [← this]
      refine rawSet_clamp_mono ?_ (STLInterval.toEReal_map_subUp_ge u (J.inf 0))
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      exact subDown_le_sub l (J.sup 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
