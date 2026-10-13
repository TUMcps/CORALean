module

public import CORALean.Global.Tensor

@[expose] public section

/-!
# The weights of a linear layer

CORA's `nnLinearLayer` as an `Enclose` kind: `W` and `b`, stored in the scalar. The layer
encloses the affine map they denote, read as reals: reading a network off a file is exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure LinearLayer (𝕋 : Type) (n m : ℕ) where
  W : Mat 𝕋 m n
  b : Vec 𝕋 m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
