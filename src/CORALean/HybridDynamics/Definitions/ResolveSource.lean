module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Where an input of a component comes from

CORA's `inputBinds{i}`: row `j` of `inputBinds{i}` is `[c l]`, and input `j` of component `i` is
either the `l`-th global input (`c = 0`) or the `l`-th output of component `c`. `resolve` of a
reset (`linearReset/resolve`, `nonlinearReset/resolve`) substitutes the second kind away;
`ParallelHybridAutomaton.binds` is CORA's `bindsInputs`, and `mergeFlowsLinearSys` merges the
components' flows through it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- Where an input of a component comes from: a global input, or an output of another component. -/
inductive ResolveSource (k : ℕ) (p : Fin k → ℕ) (g : ℕ) : Type where
  | global (a : Fin g) : ResolveSource k p g
  | output (c : Fin k) (l : Fin (p c)) : ResolveSource k p g
  deriving DecidableEq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
