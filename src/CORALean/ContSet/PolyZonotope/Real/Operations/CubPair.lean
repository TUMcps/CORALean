module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# The pairing of `cubMap`

`(xᵀ T{i,k} x) * x` is a pairing of `x` with the vector of quadratic forms
`w = (xᵀ T{i,k} x)` over the pairs `(i, k)`, `zᵢ = Σₖ xₖ · w(i, k)`: bilinear in `(x, w)`, so it is
`bilin`'s `f`. The pairs are one index `Fin (m * n)` through `finProdFinEquiv`, which is what
`quadBilin` takes as its outputs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(x, w) ↦ (Σₖ xₖ · w(i, k))ᵢ`, `w` indexed by the pairs `(i, k)`. -/
def PolyZonotope.cubPair (m n : ℕ) : Vec ℝ n →ₗ[ℝ] Vec ℝ (m * n) →ₗ[ℝ] Vec ℝ m :=
  LinearMap.mk₂ ℝ (fun (x : Vec ℝ n) (w : Vec ℝ (m * n)) (i : Fin m) =>
      ∑ k, x k * w (finProdFinEquiv (i, k)))
    (fun _ _ _ => funext fun _ => by simp [add_mul, Finset.sum_add_distrib])
    (fun _ _ _ => funext fun _ => by simp [Finset.mul_sum, mul_assoc])
    (fun _ _ _ => funext fun _ => by simp [mul_add, Finset.sum_add_distrib])
    (fun _ _ _ => funext fun _ => by simp [Finset.mul_sum, mul_left_comm])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
