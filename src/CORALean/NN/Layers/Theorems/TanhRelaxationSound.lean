module

public import CORALean.NN.Layers.Operations.TanhRelaxation
public import CORALean.NN.Layers.Theorems.DoubleRoundingSound
public import CORALean.NN.Layers.Theorems.OfAffineConjSound
public import CORALean.NN.Layers.Theorems.SigmoidRelaxationSound
public import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid

@[expose] public section

/-!
# The tanh relaxation is sound

The sigmoid relaxation's soundness, transported along the conjugation identity.
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

theorem tanhRelaxation_sound (k : ℕ) : (tanhRelaxation (𝕋 := 𝕋) k).Sound Real.tanh :=
  Relaxation.ofAffineConj_sound (sigmoidRelaxation_sound k) doubleRounding_sound
    doubleRounding_sound (by norm_num) (by norm_num)
    (fun t => by rw [toReal_neg, toReal_one, Real.tanh_eq_sigmoid]; ring)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
