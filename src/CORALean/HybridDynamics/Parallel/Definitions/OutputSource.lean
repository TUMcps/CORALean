module

public import Mathlib.Data.Fin.Basic

@[expose] public section

/-!
# Where a component's input comes from, CORA's `bindsInputs`

One row of CORA's `bindsInputs{i}`: input `j` of component `i` is either global input `a`
(`[0, a]`) or output `s` of component `c` (`[c, s]`), `q c` being that component's number of
outputs. `InputSource` is the same with states in place of outputs, the canonical-form reading
the product automaton runs on; this is the reading of the components' full equations, which
`mergeFlowsLinearSys` merges.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

inductive OutputSource (k : ℕ) (q : Fin k → ℕ) (m : ℕ) : Type where
  | global (a : Fin m) : OutputSource k q m
  | output (c : Fin k) (s : Fin (q c)) : OutputSource k q m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
