import CORALean.HybridDynamics.Definitions.NonlinearReset
import CORALean.HybridDynamics.Definitions.ResolveSource
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card

/-!
# `NonlinearReset.globalColumns`

CORA's `numGlobalInputs = nnz(idxGlobalInput)` in `nonlinearReset/resolve`: how many inputs of
the components are bound to a global input, counted with repetitions.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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
