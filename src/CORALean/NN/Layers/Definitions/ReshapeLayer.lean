import CORALean.Global.Mathlib

/-!
# The weights of a reshape layer

CORA's `nnReshapeLayer` as an `Enclose` kind: the relabelling `e`, output `i` reading input
`e i`. It stores no scalar, so it is one kind at every scalar.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure ReshapeLayer (n m : ℕ) where
  e : Fin m ≃ Fin n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
