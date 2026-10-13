import Mathlib.Data.Real.Basic

/-!
# The input-neuron orderings

CORA's `method` of `getInputNeuronOrder`: `'in-order'`, `'sensitivity'`, `'snake'`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

inductive InputOrderMethod where
  | inOrder
  | sensitivity
  | snake

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
