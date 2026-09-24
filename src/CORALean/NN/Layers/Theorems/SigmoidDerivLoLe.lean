import CORALean.NN.Layers.Definitions.Sigmoid
import CORALean.NN.Layers.Operations.SigmoidDerivLo
import CORALean.NN.Layers.Theorems.Real.SigmoidMono
import CORALean.NN.Layers.Theorems.Real.SigmoidPos

/-!
# The sigmoid derivative is above its rounded lower bound

Both factors are non-negative lower bounds on the two sigmoids, which is what makes their
rounded-down product one on the derivative.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidDerivLo_le {E : Enclosure 𝕋} (hE : E.Sound Real.sigmoid) (l u : 𝕋) (x : ℝ)
    (hl : toReal l ≤ x) (hu : x ≤ toReal u) :
    toReal (sigmoidDerivLo E l u) ≤ Real.sigmoidDeriv x := by -- --- PROOF ---
  have h₁ : toReal (maximum zero (E.lo l)) ≤ Real.sigmoid x := by
    rw [toReal_maximum, toReal_zero]
    exact max_le (le_of_lt (Real.sigmoid_pos x)) (le_trans (hE.lo_le l) (Real.sigmoid_mono hl))
  have h₂ : toReal (maximum zero (E.lo (neg u))) ≤ Real.sigmoid (-x) := by
    rw [toReal_maximum, toReal_zero]
    refine max_le (le_of_lt (Real.sigmoid_pos _)) (le_trans (hE.lo_le (neg u)) ?_)
    rw [toReal_neg]
    exact Real.sigmoid_mono (neg_le_neg hu)
  -- both factors are non-negative lower bounds, which is what makes the product one
  have h₀ : 0 ≤ toReal (maximum zero (E.lo (neg u))) := by
    rw [toReal_maximum, toReal_zero]
    exact le_max_left _ _
  rw [sigmoidDerivLo, Real.sigmoidDeriv]
  exact le_trans (mulDown_le_mul _ _)
    (mul_le_mul h₁ h₂ h₀ (le_of_lt (Real.sigmoid_pos x)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
