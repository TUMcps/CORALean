module

public import CORALean.Specification.STLInterval.Operations.Minus
public import CORALean.Specification.STLInterval.Theorems.RawSetClampMono
public import CORALean.Specification.STLInterval.Theorems.RawSetMono
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.RawSetSub
public import CORALean.Specification.STLInterval.Theorems.SetClamp
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.Theorems.ToERealMapSubUpGe

@[expose] public section

/-!
# `minus` over a float scalar encloses the difference

Over a float scalar `minus` rounds the lower bound down and the upper one up before the cut at `0`,
so it denotes every difference `≥ 0` of a time of `I` and one of `J`, and possibly more: an outward
enclosure of `set_minus`.

## Inputs
* `I` – first interval
* `J` – second interval

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

theorem STLInterval.set_minus_outer (I J : STLInterval 𝕋) : -- --- CONCL ---
    (I.set - J.set) ∩ Set.Ici 0 ⊆ (I.minus J).set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.set]
  | nonempty l₁ u₁ lc₁ rc₁ b c _ =>
    cases J with
    | empty => simp [STLInterval.set]
    | nonempty l₂ u₂ lc₂ rc₂ e f _ =>
      have h := rawSet_sub (rawSet_nonempty_of_fields b c) (rawSet_nonempty_of_fields e f)
      show (rawSet (toReal l₁ : ℝ) (toEReal u₁) lc₁ rc₁ -
        rawSet (toReal l₂ : ℝ) (toEReal u₂) lc₂ rc₂) ∩ Set.Ici 0 ⊆ _
      rw [← h]
      simp only [STLInterval.minus]
      rcases u₂ with _ | y
      · -- `lower - inf` is `-inf`: the cut to the closed `0`
        dsimp only
        have hc := rawSet_clamp_mono (l' := ⊥) (lc := lc₁ && rc₂) (rc := rc₁ && lc₂) bot_le
          (STLInterval.toEReal_map_subUp_ge u₁ l₂)
          (l := ((toReal l₁ : ℝ) : EReal) - STLInterval.toEReal (none : WithTop 𝕋))
          (u := toEReal u₁ - (toReal l₂ : ℝ))
        rw [if_pos EReal.bot_lt_zero] at hc
        rw [set_stlInterval, toReal_zero_eq, EReal.coe_zero]
        exact hc
      · dsimp only
        rw [STLInterval.set_clamp]
        refine rawSet_clamp_mono ?_ (STLInterval.toEReal_map_subUp_ge u₁ l₂)
        rw [STLInterval.toEReal_some, ← EReal.coe_sub, EReal.coe_le_coe_iff]
        exact subDown_le_sub l₁ y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
