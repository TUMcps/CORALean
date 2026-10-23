module

public import CORALean.Specification.STLInterval.Operations.MinkDiff
public import CORALean.Specification.STLInterval.Theorems.RawSetClamp
public import CORALean.Specification.STLInterval.Theorems.RawSetClampMono
public import CORALean.Specification.STLInterval.Theorems.RawSetMinkDiff
public import CORALean.Specification.STLInterval.Theorems.RawSetMono
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOfFields
public import CORALean.Specification.STLInterval.Theorems.SetClamp
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval

@[expose] public section

/-!
# `minkDiff` over a float scalar encloses the Minkowski difference

Over a float scalar `minkDiff` rounds the lower bound down and the upper one up before the cut at
`0`, so it denotes every time `t ≥ 0` with `t + J ⊆ I`, and possibly more: an outward enclosure of
`set_minkDiff`.

## Inputs
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* the times `t ≥ 0` with `t + J ⊆ I` lie in the result
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

theorem STLInterval.set_minkDiff_outer (I J : STLInterval 𝕋) : -- --- CONCL ---
    {t | 0 ≤ t ∧ ∀ y ∈ J.set, t + y ∈ I.set} ⊆ (I.minkDiff J).set := by -- --- PROOF ---
  cases J with
  | empty =>
    -- an empty `J`: every time `t ≥ 0`, all of which `[0, ∞)` holds
    rintro t ⟨h0, -⟩
    simp only [STLInterval.minkDiff]
    rw [set_stlInterval, toReal_zero_eq, STLInterval.toEReal_top]
    refine ⟨?_, Or.inl (EReal.coe_lt_top t)⟩
    rcases h0.lt_or_eq with h | h
    · exact Or.inl (EReal.coe_lt_coe_iff.2 h)
    · exact Or.inr ⟨rfl, by rw [h]⟩
  | nonempty l₂ u₂ lc₂ rc₂ e f _ =>
    cases I with
    | empty =>
      rintro t ⟨-, h⟩
      obtain ⟨y, hy⟩ := rawSet_nonempty_of_fields e f
      exact absurd (h y hy) (by simp [STLInterval.set])
    | nonempty l₁ u₁ lc₁ rc₁ b c _ =>
      have h := rawSet_minkDiff (rawSet_nonempty_of_fields b c) (rawSet_nonempty_of_fields e f)
      show {t | 0 ≤ t ∧ ∀ y ∈ rawSet (toReal l₂ : ℝ) (toEReal u₂) lc₂ rc₂,
        t + y ∈ rawSet (toReal l₁ : ℝ) (toEReal u₁) lc₁ rc₁} ⊆ _
      rw [h]
      -- the exact result is the cut of the exact bounds
      have hcut : ∀ (A UB : EReal) (lc rc : Bool), rawSet (if A < 0 then 0 else A) UB
          (if A < 0 then true else lc) rc = rawSet A UB lc rc ∩ Set.Ici 0 := by
        intro A UB lc rc
        rw [rawSet_clamp]
        split_ifs <;> rfl
      rw [hcut]
      have hlb : ((toReal (subDown l₁ l₂) : ℝ) : EReal) ≤ (toReal l₁ : ℝ) - (toReal l₂ : ℝ) := by
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
        exact subDown_le_sub l₁ l₂
      simp only [STLInterval.minkDiff]
      rcases u₁ with _ | x <;> rcases u₂ with _ | y
      · dsimp only
        rw [STLInterval.set_clamp]
        exact rawSet_clamp_mono hlb (by simp [STLInterval.subUpTop])
      · dsimp only
        rw [STLInterval.set_clamp]
        exact rawSet_clamp_mono hlb (by simp [STLInterval.subUpTop])
      · -- `upper - inf` is `-inf`: no exact time either
        intro t ht
        exfalso
        simp [rawSet] at ht
      · dsimp only
        rw [STLInterval.set_clamp]
        refine rawSet_clamp_mono hlb ?_
        rw [if_neg (by simp)]
        simp only [STLInterval.subUpTop, STLInterval.toEReal_some, ← EReal.coe_sub,
          EReal.coe_le_coe_iff]
        exact sub_le_subUp x y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
