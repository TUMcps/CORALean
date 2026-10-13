import CORALean.Global.Tensor

/-!
# The weights of a batch normalisation layer

CORA's `nnBatchNormLayer` at inference as an `Enclose` kind: a folded scale and shift per
channel, `chan` naming each coordinate's channel. The dimension is kept, so its weights carry
`dim`, the proof that the two dimensions agree, which `rfl` discharges where a layer is built.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure BatchNormLayer (𝕋 : Type) (n m : ℕ) where
  c : ℕ
  chan : Fin n → Fin c
  scale : Vec 𝕋 c
  shift : Vec 𝕋 c
  dim : n = m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
