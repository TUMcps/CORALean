module

public import CORALean.Global.Tensor

@[expose] public section

/-!
# The activations whose merge buckets CORA stores

The scalar activation functions `getMergeBuckets` is defined for here: ReLU, the logistic
function and tanh. Their functions are `ActivationKind.fn`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The activation, by name. -/
inductive ActivationKind where
  | relu
  | sigmoid
  | tanh

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
