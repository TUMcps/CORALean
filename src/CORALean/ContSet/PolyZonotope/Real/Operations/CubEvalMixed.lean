module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The mixed cubic map itself

The map of the mixed form `cubMap(S₁, S₂, S₃, T)`: `zᵢ = Σₖ (x₃)ₖ · (x₁ᵀ T{i,k} x₂)`, the three
arguments independent. `cubEval` is its diagonal `x₁ = x₂ = x₃`.

## Inputs
* `n` – dimension
* `m` – output dimension
* `T` – family of cubic form tensors
* `x₁` – first point
* `x₂` – second point
* `x₃` – third point

## Output
* value of the mixed cubic map at the three points
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The mixed cubic map `(x₁, x₂, x₃) ↦ (Σₖ (x₃)ₖ · x₁ᵀ T{i,k} x₂)ᵢ`. -/
def PolyZonotope.cubEvalMixed {n m : ℕ} (T : Fin m → Fin n → Mat ℝ n n) (x₁ x₂ x₃ : Vec ℝ n) :
    Vec ℝ m :=
  fun i => ∑ k, x₃ k * (x₁ ⬝ᵥ (T i k *ᵥ x₂))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
