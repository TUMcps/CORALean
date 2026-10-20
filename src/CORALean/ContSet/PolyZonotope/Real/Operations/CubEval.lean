module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The cubic map itself

CORA's `cubMap` computes `{ z = (xᵀ T x) * x | x ∈ S }`: with the tensor `T{i,k}` the `i`-th
output is `zᵢ = Σₖ xₖ · (xᵀ T{i,k} x)`. `cubEval` is that map; shared by the zonotope,
polynomial zonotope and constrained zonotope `cubMap`.

## Inputs
* `n` – dimension
* `m` – output dimension
* `T` – family of cubic form tensors
* `x` – point

## Output
* value of the cubic map at the point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The cubic map `x ↦ (Σₖ xₖ · xᵀ T{i,k} x)ᵢ`. -/
def PolyZonotope.cubEval {n m : ℕ} (T : Fin m → Fin n → Mat ℝ n n) (x : Vec ℝ n) : Vec ℝ m :=
  fun i => ∑ k, x k * (x ⬝ᵥ (T i k *ᵥ x))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
