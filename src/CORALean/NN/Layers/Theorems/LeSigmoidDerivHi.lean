module

public import CORALean.NN.Layers.Definitions.Sigmoid
public import CORALean.NN.Layers.Operations.SigmoidDerivHi
public import CORALean.NN.Layers.Theorems.Real.SigmoidMono
public import CORALean.NN.Layers.Theorems.Real.SigmoidPos

@[expose] public section

/-!
# The sigmoid derivative is below its rounded upper bound

Each factor is below its upper end, both non-negative, and the product rounds up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_sigmoidDerivHi {E : Enclosure 𝕋} (hE : E.Sound Real.sigmoid) (l u : 𝕋) (x : ℝ)
    (hl : toReal l ≤ x) (hu : x ≤ toReal u) :
    Real.sigmoidDeriv x ≤ toReal (sigmoidDerivHi E l u) := by -- --- PROOF ---
  -- upward the sign needs no floor: an upper bound on a positive value is positive
  have h₁ : Real.sigmoid x ≤ toReal (E.hi u) := le_trans (Real.sigmoid_mono hu) (hE.le_hi u)
  have h₂ : Real.sigmoid (-x) ≤ toReal (E.hi (neg l)) := by
    refine le_trans ?_ (hE.le_hi (neg l))
    rw [toReal_neg]
    exact Real.sigmoid_mono (neg_le_neg hl)
  rw [sigmoidDerivHi, Real.sigmoidDeriv]
  exact le_trans (mul_le_mul h₁ h₂ (le_of_lt (Real.sigmoid_pos _))
    (le_trans (le_of_lt (Real.sigmoid_pos x)) h₁)) (mul_le_mulUp _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
