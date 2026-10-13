import CORALean.Global.Tensor

/-!
# The weights of a convolutional layer

CORA's `nnConv2DLayer` as an `Enclose` kind: a kernel `K` per channel, a bias, and the
stencil `tap`, output `j` reading input `tap j l` at kernel entry `l`. The guarantee needs no
input read twice by one output, so the weights carry that `tap j` is injective.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure ConvLayer (𝕋 : Type) (n m : ℕ) where
  c : ℕ
  k : ℕ
  chan : Fin m → Fin c
  tap : Fin m → Fin k → Fin n
  K : Fin c → Fin k → 𝕋
  b : Vec 𝕋 m
  tap_injective : ∀ j, Function.Injective (tap j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
