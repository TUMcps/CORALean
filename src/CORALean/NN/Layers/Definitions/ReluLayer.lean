module

public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# The weights of a ReLU layer

CORA's `nnReLULayer` as an `Enclose` kind: its one parameter the slope rule `lam`, which is
`reluSlope` in CORA. An activation keeps the dimension, so its weights carry `dim`, the proof
that the two dimensions agree, which `rfl` discharges where a layer is built.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure ReluLayer (𝕋 : Type) (n m : ℕ) where
  lam : 𝕋 → 𝕋 → 𝕋
  dim : n = m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
