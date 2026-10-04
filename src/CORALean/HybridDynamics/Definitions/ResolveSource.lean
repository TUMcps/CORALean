import Mathlib.Data.Real.Basic

/-!
# Where an input of a component comes from

CORA's `inputBinds{i}`: row `j` of `inputBinds{i}` is `[c l]`, and input `j` of component `i` is
either the `l`-th global input (`c = 0`) or the `l`-th output of component `c`. `resolve` of a
reset (`linearReset/resolve`, `nonlinearReset/resolve`) substitutes the second kind away.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

inductive ResolveSource (k : ℕ) (p : Fin k → ℕ) (g : ℕ) : Type where
  | global (a : Fin g) : ResolveSource k p g
  | output (c : Fin k) (l : Fin (p c)) : ResolveSource k p g
  deriving DecidableEq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
