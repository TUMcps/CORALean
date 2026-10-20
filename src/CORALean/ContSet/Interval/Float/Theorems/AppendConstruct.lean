module

public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Interval.append` is the product box

The stacked box holds exactly the vectors whose first `n₁` coordinates lie in the first box and
the last `n₂` in the second, which is the image of the pair of boxes under `Fin.append`.

## Inputs
* `I₁` – first interval box
* `I₂` – second interval box

## Hypotheses
* none

## Conclusion
* the appended box is the image of the product of the two sets under concatenation
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.append_construct (I₁ : Interval (Vec 𝕋 n₁)) (I₂ : Interval (Vec 𝕋 n₂)) :
    (I₁.append I₂).construct = (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
      (I₁.construct ×ˢ I₂.construct) := by -- --- PROOF ---
  ext e
  constructor
  · intro he
    -- the two halves of `e`, each coordinate read at the matching bound
    refine ⟨(fun i => e (Fin.castAdd n₂ i), fun i => e (Fin.natAdd n₁ i)),
      ⟨fun i => ?_, fun i => ?_⟩, ?_⟩
    · have h : toReal (Fin.append I₁.inf I₂.inf (Fin.castAdd n₂ i)) ≤ e (Fin.castAdd n₂ i) ∧
          e (Fin.castAdd n₂ i) ≤ toReal (Fin.append I₁.sup I₂.sup (Fin.castAdd n₂ i)) :=
        he (Fin.castAdd n₂ i)
      simp only [Fin.append_left] at h
      exact h
    · have h : toReal (Fin.append I₁.inf I₂.inf (Fin.natAdd n₁ i)) ≤ e (Fin.natAdd n₁ i) ∧
          e (Fin.natAdd n₁ i) ≤ toReal (Fin.append I₁.sup I₂.sup (Fin.natAdd n₁ i)) :=
        he (Fin.natAdd n₁ i)
      simp only [Fin.append_right] at h
      exact h
    · funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  -- conversely, each half of an appended pair is read at its own bounds
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have h : toReal (I₁.inf i) ≤ a i ∧ a i ≤ toReal (I₁.sup i) := ha i
      show toReal (Fin.append I₁.inf I₂.inf (Fin.castAdd n₂ i)) ≤ Fin.append a b (Fin.castAdd n₂ i)
        ∧ Fin.append a b (Fin.castAdd n₂ i) ≤ toReal (Fin.append I₁.sup I₂.sup (Fin.castAdd n₂ i))
      simpa only [Fin.append_left] using h
    · have h : toReal (I₂.inf i) ≤ b i ∧ b i ≤ toReal (I₂.sup i) := hb i
      show toReal (Fin.append I₁.inf I₂.inf (Fin.natAdd n₁ i)) ≤ Fin.append a b (Fin.natAdd n₁ i)
        ∧ Fin.append a b (Fin.natAdd n₁ i) ≤ toReal (Fin.append I₁.sup I₂.sup (Fin.natAdd n₁ i))
      simpa only [Fin.append_right] using h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
