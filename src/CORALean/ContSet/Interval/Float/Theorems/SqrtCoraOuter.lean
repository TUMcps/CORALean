module

public import CORALean.ContSet.Interval.Float.Operations.SqrtCora

@[expose] public section

/-!
# `Interval.sqrtCora` contains the image under `sqrt`

## Inputs
* `p` – Newton steps
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the square root image of `I` lies in the result box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       21-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The root from below is under the real one, whatever the fuel. -/
private theorem Interval.aux_sqrtDownCora_le [SoundFloatArithmetic 𝕋] (p : ℕ)
    (a : 𝕋) : -- --- CONCL ---
    toReal (sqrtDownCora p a) ≤ Real.sqrt (toReal a) := by -- --- PROOF ---
  unfold sqrtDownCora
  split
  · rename_i f hf
    refine SoundFloatArithmetic.sqrtDownOverride_le hf p a _ (Real.sqrt_nonneg _) ?_
    rcases le_total 0 (toReal a) with h | h
    · rw [Real.mul_self_sqrt h]; exact max_le le_rfl h
    · rw [Real.sqrt_eq_zero_of_nonpos h]; simpa using h
  · exact sqrtDown_le p a


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sqrtCora_outer [SoundFloatArithmetic 𝕋] (p : ℕ) (I : Interval (Vec 𝕋 n)) :
    (fun x i => Real.sqrt (x i)) '' I.toSet ⊆ (I.sqrtCora p).toSet := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  exact ⟨le_trans (Interval.aux_sqrtDownCora_le p _) (Real.sqrt_le_sqrt hx'.1),
    le_trans (Real.sqrt_le_sqrt hx'.2) (le_sqrtUp p _)⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
