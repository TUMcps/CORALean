import CORALean.NN.Operations.WeightNetworkNormalForm
import CORALean.NN.Theorems.WeightNetworkNormalFormAuxEval

/-!
# The normal form computes the same function

`getNormalForm` fuses layers without changing what the network computes, exactly, for linear,
elementwise affine and identity layers between any activations. Over any semiring, so at ℝ the
fused weights are the exact products.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {α : Type} [Semiring α] {n m k d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The normal form and the network compute the same function. -/
theorem WeightNetwork.normalForm_eval (N : WeightNetwork α n k) (x : Fin n → α) :
    N.normalForm.eval x = N.eval x :=
  N.normalFormAux_eval .id x

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
