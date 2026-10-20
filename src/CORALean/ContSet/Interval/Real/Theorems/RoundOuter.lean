module

public import CORALean.ContSet.Interval.Real.Operations.Round
public import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageOuter

@[expose] public section

/-!
# `Interval.round` contains the image under the rounding

`roundAway` is monotone but a step function, so the image of a box is a finite set of integers,
not a box: only the outer statement holds, with no hypothesis.

## Inputs
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the rounded image of `I` lies in the result box
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_roundAway_monotone : -- --- CONCL ---
    Monotone roundAway := by -- --- PROOF ---
  intro a b hab
  unfold roundAway
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    rw [if_pos ha, if_pos hb]
    exact_mod_cast Int.floor_mono (by linarith)
  · by_cases hb : 0 ≤ b
    · rw [if_neg ha, if_pos hb]
      have h1 : (0 : ℝ) ≤ ⌊-a + 1 / 2⌋ := by exact_mod_cast Int.floor_nonneg.2 (by linarith)
      have h2 : (0 : ℝ) ≤ ⌊b + 1 / 2⌋ := by exact_mod_cast Int.floor_nonneg.2 (by linarith)
      linarith
    · rw [if_neg ha, if_neg hb]
      have : ⌊-b + 1 / 2⌋ ≤ ⌊-a + 1 / 2⌋ := Int.floor_mono (by linarith)
      have : (⌊-b + 1 / 2⌋ : ℝ) ≤ ⌊-a + 1 / 2⌋ := by exact_mod_cast this
      linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.round_outer (I : Interval (Vec ℝ n)) :
    (fun x i => roundAway (x i)) '' I.construct ⊆ I.round.construct :=
  Interval.monotoneImage_outer roundAway aux_roundAway_monotone I


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
