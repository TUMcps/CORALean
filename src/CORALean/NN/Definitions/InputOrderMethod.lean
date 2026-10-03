import Mathlib.Data.Real.Basic

/-!
# The input-neuron orderings

CORA's `method` of `getInputNeuronOrder`: `'in-order'`, `'sensitivity'`, `'snake'`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

inductive InputOrderMethod where
  | inOrder
  | sensitivity
  | snake

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
