module

public import CORALean.NN.Layers.Definitions.PolyRelaxation

@[expose] public section

/-!
# The weights of a polynomial activation layer

Any coordinatewise activation at a polynomial zonotope as an `Enclose` kind: a polynomial
relaxation per neuron of degree `deg`, and a proof that all of them enclose *some* one `σ`,
a `Prop` for `ActivationLayer`'s reason. The dimension is kept, so its weights carry `dim`,
the proof that the two dimensions agree, which `rfl` discharges where a layer is built.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure ActivationPolyLayer (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
    (n m : ℕ) where
  deg : ℕ
  P : LayerRelaxation 𝕋 n deg
  sound : ∃ σ : ℝ → ℝ, ∀ i, (P i).Sound σ
  dim : n = m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
