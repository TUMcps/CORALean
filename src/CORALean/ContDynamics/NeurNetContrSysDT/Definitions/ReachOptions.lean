module

public import Mathlib.Data.Nat.Basic

@[expose] public section

/-!
# CORA's `options` for a discrete-time neural-network-controlled reach

`ρ`, as `LinearSysDT.ReachOptions` has it: the order every step of the plant is reduced to.
CORA's `neurNetContrSys/reach` also reads `options.nn`, the settings of its network verifier;
`NeuralNetwork.enclose` fixes those here. `hZonotopeOrder` rules out `0`: at `o = 0`,
`Zonotope.reduceGirard`'s natural subtraction silently returns order 1, where CORA's `geone`
check refuses the value. Its default proof closes it at any positive literal.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The maximum order `ρ` every step is reduced to, positive. -/
structure NeurNetContrSysDT.ReachOptions where
  ρ : ℕ
  hZonotopeOrder : 0 < ρ := by exact Nat.zero_lt_succ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
