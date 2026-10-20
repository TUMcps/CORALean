module

public import CORALean.NN.Layers.Definitions.ActivationLayer

@[expose] public section

/-!
# An activation layer from a soundness proof

The weights `ActivationLayer` asks for, read off a proof that `R` encloses `σ`: the proof
becomes the existential, and `dim` is `rfl`. Two layers built this way at one `R` are equal
whatever `σ` each proof was for, which is what lets a reduced network's activation be the
original's. `macro_inline`, so `σ`, which the layer never stores, is not compiled either:
a caller at `Real.sigmoid` still runs.

## Inputs
* `R` – relaxation of the activation

## Hypotheses
* `hR` – relaxation is sound for the activation

## Output
* activation layer carrying the soundness proof
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ} {σ : ℝ → ℝ}


-- =====================================  MAIN DEFINITION  ====================================== --

@[macro_inline]
def ActivationLayer.of {R : Relaxation 𝕋} (hR : R.Sound σ) : ActivationLayer 𝕋 n n :=
  ⟨R, ⟨σ, hR⟩, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
