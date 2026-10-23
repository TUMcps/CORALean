module

public import CORALean.Specification.STLInterval.Operations.MinusNum
public import CORALean.Specification.STLInterval.Theorems.RawSetClampMono
public import CORALean.Specification.STLInterval.Theorems.RawSetMono
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.RawSetSub
public import CORALean.Specification.STLInterval.Theorems.SetClamp
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.ToERealMapSubUpGe

@[expose] public section

/-!
# `minusNum` over a float scalar encloses the shift

Over a float scalar `minusNum` rounds the lower bound down and the upper one up before the cut at
`0`, so it denotes every time of `I` shifted down by the real `c` that is `≥ 0`, and possibly more:
an outward enclosure of `set_minusNum`.

## Inputs
* `I` – interval
* `c` – number

## Hypotheses
* none

## Conclusion
* the shifted times `≥ 0` lie in the result
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

theorem STLInterval.set_minusNum_outer (I : STLInterval 𝕋) (c : 𝕋) : -- --- CONCL ---
    ((fun t => t - toReal c) '' I.set) ∩ Set.Ici 0 ⊆ (I.minusNum c).set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.set]
  | nonempty l u lc rc b c' _ =>
    have := rawSet_sub (rawSet_nonempty_of_fields b c')
      (rawSet_closed_nonempty (le_refl (toReal c)))
    rw [rawSet_closed_coe, Set.Icc_self, Set.sub_singleton] at this
    simp only [Bool.and_true] at this
    show (fun t => t - toReal c) '' rawSet (toReal l : ℝ) (toEReal u) lc rc ∩ Set.Ici 0 ⊆ _
    rw [← this]
    simp only [STLInterval.minusNum]
    rw [STLInterval.set_clamp]
    refine rawSet_clamp_mono ?_ (STLInterval.toEReal_map_subUp_ge u c)
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    exact subDown_le_sub l c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
