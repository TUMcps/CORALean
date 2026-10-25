module

public import CORALean.NN.Layers.Operations.RelaxationTighter

@[expose] public section

/-!
# The tighter of two sound relaxations is sound

Whichever branch `le` picks on a box, that relaxation is sound there.

## Inputs
* `R₁` – first relaxation
* `R₂` – second relaxation

## Hypotheses
* `h₁` – first relaxation is sound for the activation
* `h₂` – second relaxation is sound for the activation

## Conclusion
* the tighter relaxation is sound for the activation
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Both branches are sound, so a wrong answer costs precision and never soundness. -/
theorem Relaxation.tighter_sound {R₁ R₂ : Relaxation 𝕋} (h₁ : R₁.IsSound σ)
    (h₂ : R₂.IsSound σ) : -- --- CONCL ---
    (Relaxation.tighter R₁ R₂).IsSound σ := by -- --- PROOF ---
  refine ⟨fun {l u _t} hl hu => ?_⟩
  show |σ _t - (toReal (if le (R₁.error l u) (R₂.error l u) then _ else _) * _t
    + toReal (if le (R₁.error l u) (R₂.error l u) then _ else _))|
      ≤ toReal (if le (R₁.error l u) (R₂.error l u) then _ else _)
  by_cases h : le (R₁.error l u) (R₂.error l u) = true
  · rw [if_pos h, if_pos h, if_pos h]
    exact h₁.sound hl hu
  · rw [if_neg h, if_neg h, if_neg h]
    exact h₂.sound hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
