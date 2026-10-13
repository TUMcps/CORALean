import Mathlib.Data.Nat.Basic

/-!
# CORA's `options` for a discrete-time linear reach at a per-step order

`ρ` as a sequence, one order per step, where `ReachOptions` holds the
one order every step shares. CORA's `linearSysDT` reach takes a single
`ρ`; a per-step choice is the tuning of Wetzlinger et al., and the
`o (k + 1)` it takes at step `k + 1` is the order that step is reduced to.

`hZonotopeOrder` rules out `0` at every step, as `ReachOptions.hZonotopeOrder`
does at the one order. No default proof closes an arbitrary sequence, so a caller
brings its own.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The maximum orders `ρ k` step `k` is reduced to, all positive. -/
structure LinearSysDT.ReachOrdersOptions where
  ρ : ℕ → ℕ
  hZonotopeOrder : ∀ k, 0 < ρ k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
