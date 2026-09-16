import CORALean.ContDynamics.LinearSys.Theorems.IntegralReachSetSubset
import CORALean.ContDynamics.LinearSys.Theorems.IntegralReachSetSuperset

/-!
# The integral reachable set is exactly the closed form

`integralReachSet`, evaluated at `T`'s own right endpoint so `t ∈ T` always,
equals `e^{tA} R₀ ⊕ inputReach U t` outright — `reachSet`'s own closed form
only encloses, `Trajectory`'s two-sided derivative excluding the
piecewise-constant inputs a witness in `inputReach` can name.
`IntegralReachSetSubset`/`IntegralReachSetSuperset` are the two halves.
-/

-- Authors:       Tobias Ladner
-- Written:       15-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The integral-equation reachable set at `t` is exactly `e^{tA} R₀ ⊕ inputReach U t`. -/
theorem LinearSys.integralReachSet_eq (sys : LinearSys 𝕋 n) (R₀ U : S n) {t : ℝ} (ht : 0 ≤ t)
    (hU : Bornology.IsBounded (construct U)) :
    sys.integralReachSet (Set.Icc 0 t) R₀ U t
      = (exp (t • toRealMat sys.A)).mulVecLin '' construct R₀ + sys.inputReach U t :=
  Set.Subset.antisymm
    (sys.integralReachSet_subset_mulVecLin_image_add_inputReach R₀ U ht hU)
    (sys.mulVecLin_image_add_inputReach_subset_integralReachSet R₀ U ht hU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
