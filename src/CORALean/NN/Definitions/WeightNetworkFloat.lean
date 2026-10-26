module

public import CORALean.NN.Definitions.WeightLayerFloat

@[expose] public section

/-!
# A float network of weight layers
`WeightNetwork` over the float layers: the layers applied first to last, weights in boxes of
floats.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable (𝕋 : Type) [FloatOps 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- Layers applied first to last. -/
inductive WeightNetwork : ℕ → ℕ → Type where
  | nil {n : ℕ} : WeightNetwork n n
  | cons {n m k : ℕ} (L : WeightLayer 𝕋 n m) (rest : WeightNetwork m k) : WeightNetwork n k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
