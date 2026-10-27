module

public import CORALean.ContSet.Interval.Float.Operations.Round
public import CORALean.ContSet.Interval.Real.Operations.RoundAway
public import CORALean.ContSet.Interval.Real.Operations.Round

@[expose] public section

/-!
# `Interval.round` encloses the exact rounding

Outer: the exact layer's `Interval.round` of the nominal box is inside the float result's
construct, so, with the exact layer's `round_outer`, is the rounding of every point of the nominal
box. The bounds are the integers `roundAway` of the scalars' exact values, between `intDown` and
`intUp` of themselves.

## Inputs
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the exact rounded box lies in the float one
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `step_roundAwayInt` is `roundAway`. -/
private theorem aux_roundAwayInt_cast (q : ℚ) : -- --- CONCL ---
    ((step_roundAwayInt q : ℤ) : ℝ) = CORALean.Real.roundAway (q : ℝ) := by -- --- PROOF ---
  unfold step_roundAwayInt CORALean.Real.roundAway
  by_cases h : 0 ≤ q
  · have h' : (0 : ℝ) ≤ q := by exact_mod_cast h
    rw [if_pos h, if_pos h']
    have := Rat.floor_cast (α := ℝ) (q + 1 / 2)
    push_cast at this
    rw [← this]
  · have h' : ¬ (0 : ℝ) ≤ q := by exact_mod_cast h
    rw [if_neg h, if_neg h']
    have := Rat.floor_cast (α := ℝ) (-q + 1 / 2)
    push_cast at this ⊢
    rw [← this]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.round_outer (I : Interval (Vec 𝕋 n)) : -- --- CONCL ---
    I.nominal.round.construct ⊆ I.round.construct := by -- --- PROOF ---
  intro x hx i
  have h := hx i
  have hl : CORALean.Real.roundAway (toReal (I.inf i)) =
      ((step_roundAwayInt (ToRat.toRat (I.inf i)) : ℤ) : ℝ) := by
    rw [aux_roundAwayInt_cast, ToRat.toReal_toRat]
  have hu : CORALean.Real.roundAway (toReal (I.sup i)) =
      ((step_roundAwayInt (ToRat.toRat (I.sup i)) : ℤ) : ℝ) := by
    rw [aux_roundAwayInt_cast, ToRat.toReal_toRat]
  have h1 := (intDown_le_intUp (𝕋 := 𝕋) (step_roundAwayInt (ToRat.toRat (I.inf i)))).1
  have h2 := (intDown_le_intUp (𝕋 := 𝕋) (step_roundAwayInt (ToRat.toRat (I.sup i)))).2
  refine ⟨?_, ?_⟩
  · exact le_trans h1 (hl ▸ h.1)
  · exact le_trans (hu ▸ h.2) h2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
