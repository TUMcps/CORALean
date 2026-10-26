module

public import CORALean.NN.Definitions.WeightNetworkFloat
public import CORALean.NN.Definitions.WeightNetwork
public import CORALean.NN.Definitions.WeightLayerEnclosesFloat

@[expose] public section

/-!
# A float network stands for a real one
`WeightNetwork.Encloses N N'`: the two networks have the same layers, each float layer standing
for the real one (`WeightLayer.Encloses`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- Layer by layer, the real network is enclosed by the float one. -/
inductive WeightNetwork.Encloses : ∀ {n m : ℕ}, WeightNetwork 𝕋 n m →
    CORALean.WeightNetwork ℝ n m → Prop where
  | nil {n : ℕ} : Encloses (.nil : WeightNetwork 𝕋 n n) .nil
  | cons {n m k : ℕ} {L : WeightLayer 𝕋 n m} {L' : CORALean.WeightLayer ℝ n m}
      {rest : WeightNetwork 𝕋 m k} {rest' : CORALean.WeightNetwork ℝ m k}
      (hL : L.Encloses L') (h : Encloses rest rest') : Encloses (.cons L rest) (.cons L' rest')

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
