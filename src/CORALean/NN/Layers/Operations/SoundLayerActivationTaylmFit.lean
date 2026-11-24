module

public import CORALean.NN.Layers.Definitions.SoundLayer
public import CORALean.NN.Layers.Theorems.ActivationTaylmFitEncloses
public import CORALean.NN.Layers.Theorems.Basic

@[expose] public section

/-!
# The activation layer on Taylor models as a packed layer

`Layer.activationTaylmFit` with the function it encloses, `σ` coordinatewise, and the guarantee
(`Layer.activationTaylmFit_encloses`), the form `NeuralNetwork.layer` takes.

## Inputs
* `P` – the fit of every neuron
* `top` – the degree of every neuron's fit on a box
* `σ` – the activation, held `Erased`

## Hypotheses
* `hP` – every fit is sound for `σ`
* `hz` – a coefficient above the degree `top` is zero

## Output
* the packed layer
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n deg d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SoundLayer.activationTaylmFit (P : LayerRelaxation 𝕋 n deg) (top : Fin n → 𝕋 → 𝕋 → ℕ)
    (σ : Erased (ℝ → ℝ)) (hP : ∀ i, (P i).Encloses σ.out)
    (hz : ∀ i l u (k : Fin deg), top i l u ≤ k → toReal ((P i).coeffs l u k.succ) = 0) :
    SoundLayer (TaylmArray 𝕋 d) n n where
  eval := Erased.mk fun x i => σ.out (x i)
  enclose := (Layer.activationTaylmFit P top).enclose
  enclose_outer s := by
    rw [Erased.out_mk]
    exact (Layer.activationTaylmFit_encloses hP hz).image_subset s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
