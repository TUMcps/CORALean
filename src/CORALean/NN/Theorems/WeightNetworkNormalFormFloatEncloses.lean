module

public import CORALean.NN.Operations.WeightNetworkNormalFormFloat
public import CORALean.NN.Operations.WeightNetworkNormalForm
public import CORALean.NN.Theorems.WeightNetworkNormalFormAuxFloatEncloses

@[expose] public section

/-!
# The float normal form encloses the real one
A float network that encloses a real one has a normal form that encloses the real normal form: the
fused layers, the same number of them, with the real fused weights `W₂ W₁`, `W₂ b₁ + b₂` in the
rounded boxes (and the real normal form computes the real network's function,
`WeightNetwork.normalForm_eval`).

## Inputs
* `N` – float weight network
* `N'` – real weight network

## Hypotheses
* `h` – the float network encloses the real one

## Conclusion
* the float normal form encloses the real normal form
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem WeightNetwork.normalForm_encloses {N : WeightNetwork 𝕋 n k}
    {N' : CORALean.WeightNetwork ℝ n k} (h : N.Encloses N') :
    N.normalForm.Encloses N'.normalForm :=
  WeightNetwork.normalFormAux_encloses (acc := .id) (acc' := .id)
    (by simp only [WeightAcc.Encloses]) h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
