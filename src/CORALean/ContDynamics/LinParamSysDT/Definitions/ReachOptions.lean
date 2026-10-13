import Mathlib.Data.Nat.Basic

/-!
# CORA's `options` for a discrete-time set-valued-matrix reach

`ρ`, as `LinearSysDT.ReachOptions` has it: the one option this
reach reads. The matrix set `sys.A` is multiplied through `Mtimes`, and
CORA's default of `inf`, no reduction, has no value in `ℕ`, so the order is
mandatory.

`hZonotopeOrder` rules out `0`, as the positional `ho` did: at `o = 0`,
`Zonotope.reduceGirard`'s natural subtraction keeps `(0 - 1) · n = 0` generators
and silently returns order 1, where CORA's `geone` check refuses the value. Its
default proof closes it at any positive literal, so a literal order costs a
caller nothing; an order held in a variable brings its own proof.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The maximum order `ρ` every step is reduced to, positive. -/
structure LinParamSysDT.ReachOptions where
  ρ : ℕ
  hZonotopeOrder : 0 < ρ := by exact Nat.zero_lt_succ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
