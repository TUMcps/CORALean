import Mathlib.Data.Set.Prod

/-!
# The weights of a reshape layer

CORA's `nnReshapeLayer` as an `Enclose` kind: the relabelling `e`, output `i` reading input
`e i`. It stores no scalar, so it is one kind at every scalar.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure ReshapeLayer (n m : ℕ) where
  e : Fin m ≃ Fin n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
