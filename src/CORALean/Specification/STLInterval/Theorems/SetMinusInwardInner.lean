module

public import CORALean.Specification.STLInterval.Operations.MinusInward
public import CORALean.Specification.STLInterval.Theorems.RawSetClamp
public import CORALean.Specification.STLInterval.Theorems.RawSetMono
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.RawSetSub
public import CORALean.Specification.STLInterval.Theorems.SetClamp
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `minusInward` lies inside the difference

`minusInward` rounds the lower bound up and the upper one down before the cut at `0`, so every time
it denotes is a difference `≥ 0` of a time of `I` and one of `J`: an inner approximation of
`set_minus`, where `set_minus_outer` is the outer one.

## Inputs
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* the result holds only differences `≥ 0`
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ExactLe 𝕋] in
/-- Moving an upper bound down by `c` with `subDown` lands at most at the exact bound. -/
private theorem STLInterval.aux_toEReal_map_subDown_le (u : WithTop 𝕋) (c : 𝕋) : -- --- CONCL ---
    STLInterval.toEReal (u.map (subDown · c)) ≤
      STLInterval.toEReal u - (toReal c : ℝ) := by -- --- PROOF ---
  cases u with
  | top => simp
  | coe x =>
    simp only [WithTop.map_coe, STLInterval.toEReal_coe, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    exact subDown_le_sub x c


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.set_minusInward_inner (I J : STLInterval 𝕋) : -- --- CONCL ---
    (I.minusInward J).set ⊆ (I.set - J.set) ∩ Set.Ici 0 := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.minusInward, STLInterval.set]
  | nonempty l₁ u₁ lc₁ rc₁ b c _ =>
    cases J with
    | empty => simp [STLInterval.minusInward, STLInterval.set]
    | nonempty l₂ u₂ lc₂ rc₂ e f _ =>
      -- the difference is the times between the exact bounds
      have h := rawSet_sub (rawSet_nonempty_of_fields b c) (rawSet_nonempty_of_fields e f)
      show _ ⊆ (rawSet (toReal l₁ : ℝ) (toEReal u₁) lc₁ rc₁ -
        rawSet (toReal l₂ : ℝ) (toEReal u₂) lc₂ rc₂) ∩ Set.Ici 0
      rw [← h, rawSet_clamp]
      simp only [STLInterval.minusInward]
      rcases u₂ with _ | y
      · -- `lower - inf` is `-inf`: both are cut to the closed `0`
        dsimp only
        rw [if_pos (by simp), set_stlInterval, toReal_zero_eq, EReal.coe_zero]
        exact rawSet_mono le_rfl (STLInterval.aux_toEReal_map_subDown_le u₁ l₂)
      · -- the rounded bounds lie between the exact ones
        dsimp only
        rw [STLInterval.set_clamp, ← rawSet_clamp, ← rawSet_clamp]
        refine Set.inter_subset_inter_left _ (rawSet_mono ?_
          (STLInterval.aux_toEReal_map_subDown_le u₁ l₂))
        rw [STLInterval.toEReal_some, ← EReal.coe_sub, EReal.coe_le_coe_iff]
        exact sub_le_subUp l₁ y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
