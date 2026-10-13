module

public import CORALean.HybridDynamics.Definitions.NonlinearReset
public import CORALean.HybridDynamics.Definitions.ResolveSource
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# `NonlinearReset.globalColumns`

CORA's `numGlobalInputs = nnz(idxGlobalInput)` in `nonlinearReset/resolve`: how many inputs of
the components are bound to a global input, counted with repetitions.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {N g k : ℕ} {n m p : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

-- The number of globally bound inputs, CORA's `numGlobalInputs = nnz(idxGlobalInput)`.
def NonlinearReset.globalColumns (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g) : ℕ :=
  (Finset.univ.filter fun ij : (Σ i, Fin (m i)) =>
    ∃ a, inputBinds ij.1 ij.2 = .global a).card

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
