module

public import CORALean.NN.Layers.Operations.TanhPolyRelaxation
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Layers.Theorems.PolyRelaxationOfAffineConjSound
public import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid
public import CORALean.NN.Layers.Theorems.SigmoidPolyRelaxationSound

@[expose] public section

/-!
# The polynomial tanh relaxation is sound

The sigmoid's soundness, transported along the conjugation identity `tanh t = 2 σ(2t) - 1`.

## Inputs
* `k` – reduction depth of the exponential
* `c` – fit coefficients for each box
* `dx` – grid spacing for each box
* `p` – proposed sample grid for each box

## Hypotheses
* none

## Conclusion
* the polynomial relaxation is sound for tanh
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   12-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem tanhPolyRelaxation_sound (k : ℕ) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (dx : 𝕋 → 𝕋 → 𝕋)
    (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) : (tanhPolyRelaxation k c dx p).Sound Real.tanh :=
  PolyRelaxation.ofAffineConj_sound (sigmoidPolyRelaxation_sound k c dx p) doubleRounding_sound
    doubleRounding_sound (by norm_num) (by norm_num)
    (fun t => by rw [toReal_neg, toReal_one, Real.tanh_eq_sigmoid]; ring)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
