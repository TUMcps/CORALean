module

public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# The weights of a softmax layer

CORA's `nnSoftmaxLayer` as an `Enclose` kind: its one parameter `k`, how many terms enclose
`exp`. Every output reads every input, but the dimension is kept, so its weights carry `dim`,
the proof that the two dimensions agree, which `rfl` discharges where a layer is built.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The weights of a softmax layer: the number `k` of terms enclosing `exp`. -/
structure SoftmaxLayer (𝕋 : Type) (n m : ℕ) where
  k : ℕ
  dim : n = m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
