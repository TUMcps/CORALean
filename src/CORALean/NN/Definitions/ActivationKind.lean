import CORALean.Global.Tensor

/-!
# The activations whose merge buckets CORA stores

The scalar activation functions `getMergeBuckets` is defined for here: ReLU, the logistic
function and tanh. Their functions are `ActivationKind.fn`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


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
