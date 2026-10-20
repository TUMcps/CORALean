module

public import Mathlib.Data.Nat.Basic

@[expose] public section

/-!
# CORA's `options` for a discrete-time linear reach

`ρ`, the one option CORA's `config_linearSysDT_reach` makes mandatory. CORA's default is `inf`,
no reduction at all, which `ℕ` has no value for. `hZonotopeOrder` rules out `0`: at `o = 0`,
`Zonotope.reduceGirard`'s natural subtraction silently returns order 1, where CORA's `geone`
check refuses the value. Its default proof closes it at any positive literal; an order held in
a variable brings its own proof.
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The maximum order `ρ` every step is reduced to, positive. -/
structure LinearSysDT.ReachOptions where
  ρ : ℕ
  hZonotopeOrder : 0 < ρ := by exact Nat.zero_lt_succ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
