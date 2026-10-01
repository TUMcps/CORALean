import CORALean.HybridDynamics.Parallel.Definitions.ExactScalar

/-!
# What the parallel automaton instantiates

`ExactScalar` at `ℝ`, the one scalar whose sum is exact: the entry-wise reading is the identity,
so every law is `rfl`. A rounded scalar has none, and assembles a product some other way (#40).
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  INSTANCES  ========================================= --

/-- `ℝ` reads itself back, entry by entry. -/
instance : ExactScalar ℝ where
  toReal := id
  toRealMat_apply _ _ _ := rfl
  toRealVec_apply _ _ := rfl
  toReal_zero := rfl
  toReal_one := rfl
  toReal_add _ _ := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
