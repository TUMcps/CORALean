module

public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# The weights of a tanh layer

CORA's `nnTanhLayer` as an `Enclose` kind: its one parameter `k`, how many terms enclose
`exp`. An activation keeps the dimension, so its weights carry `dim`, the proof that the two
dimensions agree, which `rfl` discharges where a layer is built.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure TanhLayer (𝕋 : Type) (n m : ℕ) where
  k : ℕ
  dim : n = m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
