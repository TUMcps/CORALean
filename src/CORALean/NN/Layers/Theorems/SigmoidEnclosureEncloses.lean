module

public import CORALean.NN.Layers.Definitions.Sigmoid
public import CORALean.NN.Layers.Operations.SigmoidEnclosure

@[expose] public section

/-!
# The logistic function's enclosure is sound

Where `Real.sigmoid` first appears: the enclosure names no real function. Each end asks only
that the denominator be underestimated, which `expDown_le` gives; the lower end reads `σ` as
`1 - (1 + eᵗ)⁻¹` so that it, too, needs only a lower bound on an exponential.

## Inputs
* `k` – reduction depth of the exponential

## Hypotheses
* none

## Conclusion
* the enclosure brackets the sigmoid at every stored number
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_one_le_onePlusExpDown (k : ℕ) (a : 𝕋) : 1 ≤ toReal (onePlusExpDown k a) := by
  rw [onePlusExpDown, toReal_maximum, toReal_one]
  exact le_max_left _ _

private theorem aux_onePlusExpDown_le (k : ℕ) (a : 𝕋) : -- --- CONCL ---
    toReal (onePlusExpDown k a) ≤ 1 + Real.exp (toReal a) := by -- --- PROOF ---
  rw [onePlusExpDown, toReal_maximum]
  refine max_le ?_ (le_trans (addDown_le_add one (expDown k a)) ?_)
  · rw [toReal_one]
    linarith [Real.exp_pos (toReal a)]
  · rw [toReal_one]
    linarith [expDown_le k a]

/-- `σ` written so that only a *lower* bound on `exp` is needed. -/
private theorem aux_sigmoid_eq (t : ℝ) : -- --- CONCL ---
    Real.sigmoid t = 1 - (1 + Real.exp t)⁻¹ := by -- --- PROOF ---
  have hpos : (0:ℝ) < Real.exp t := Real.exp_pos t
  have hE : Real.exp t ≠ 0 := ne_of_gt hpos
  have h1 : (1:ℝ) + Real.exp t ≠ 0 := by positivity
  have h2 : (1:ℝ) + (Real.exp t)⁻¹ ≠ 0 := by positivity
  rw [Real.sigmoid, Real.exp_neg]
  field_simp
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- `sigmoidEnclosure` brackets `Real.sigmoid` at every stored value. -/
theorem sigmoidEnclosure_encloses (k : ℕ) :
    (sigmoidEnclosure (𝕋 := 𝕋) k).Encloses Real.sigmoid where
  lo_le a := by
    have hb := one_div_le_divUp (aux_one_le_onePlusExpDown k a) (aux_onePlusExpDown_le k a)
    have hs := subDown_le_sub one (divUp one (onePlusExpDown k a))
    rw [toReal_one] at hs
    show toReal (subDown one (divUp one (onePlusExpDown k a))) ≤ _
    rw [aux_sigmoid_eq (toReal a), ← one_div]
    linarith
  -- the upper end is `1/(1 + e⁻ᵗ)` directly, which is why it needs no subtraction
  le_hi a := by
    have hb := one_div_le_divUp (aux_one_le_onePlusExpDown k (neg a))
      (aux_onePlusExpDown_le k (neg a))
    rw [toReal_neg] at hb
    show _ ≤ toReal (divUp one (onePlusExpDown k (neg a)))
    rw [Real.sigmoid, ← one_div]
    exact hb

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
