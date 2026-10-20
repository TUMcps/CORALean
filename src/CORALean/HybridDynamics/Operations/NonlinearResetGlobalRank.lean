module

public import CORALean.HybridDynamics.Definitions.NonlinearReset
public import CORALean.HybridDynamics.Definitions.ResolveSource
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# `NonlinearReset.globalRank`

The position of a globally bound input among the globally bound ones, in the order of
`idxCompInput`: the index of `u_sym(1:numGlobalInputs)` that CORA's `subs(f_sym,
u_sym(idxGlobalInput), u_sym(1:numGlobalInputs))` replaces it by.

## Inputs
* `inputBinds` – input bindings
* `ij` – component input

## Output
* position among the globally bound inputs
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {N g k : ℕ} {n m p : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinearReset.globalRank (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g)
    (ij : Σ i, Fin (m i)) : ℕ :=
  (Finset.univ.filter fun ij' : (Σ i, Fin (m i)) =>
    (∃ a, inputBinds ij'.1 ij'.2 = .global a) ∧
      finSigmaFinEquiv ij' < finSigmaFinEquiv ij).card

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
