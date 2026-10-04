import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# The mixed cubic map itself

The map of the mixed form `cubMap(S₁, S₂, S₃, T)`: `zᵢ = Σₖ (x₃)ₖ · (x₁ᵀ T{i,k} x₂)`, the three
arguments independent. `cubEval` is its diagonal `x₁ = x₂ = x₃`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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
