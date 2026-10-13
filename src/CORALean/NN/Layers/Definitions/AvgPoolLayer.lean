import CORALean.Global.Tensor

/-!
# The weights of an average pooling layer

CORA's `nnAvgPool2DLayer` as an `Enclose` kind: the stencil `tap` and `winv`, the stored
reciprocal of the window size, which the layer encloses the sum scaled by as read. The
weights carry that `tap j` is injective, as a convolution's do.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure AvgPoolLayer (𝕋 : Type) (n m : ℕ) where
  k : ℕ
  winv : 𝕋
  tap : Fin m → Fin k → Fin n
  tap_injective : ∀ j, Function.Injective (tap j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
