import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep

/-!
# One window of `reach`, recursively: `R(τ_{k+1}) = e^{AΔt} R(τ_k)`

CORA's `standard` scheme, its default, and [1, Alg. 4]'s recursion at a point
matrix with no input and no order reduction: the first window is
`timeIntervalStep`, and every later one is the window before it carried one
step further by `e^{AΔt}`. Where `mtimes` only encloses, each step's
overapproximation is carried into all later windows and compounds, which is the
wrapping effect `reachStepkWrappingFree` avoids by applying `e^{A t_k}` to the
first window directly.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Mtimes

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` at Taylor order `η`: `R(τ_0)` is
`timeIntervalStep`, and `R(τ_{k+1}) = e^{AΔt} R(τ_k)`. -/
noncomputable def LinearSys.reachStepk (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) (X₀ : S n) :
    ℕ → S n
  | 0     => sys.timeIntervalStep Δt η X₀
  | k + 1 => mtimes (exp (Δt • toRealMat sys.A)) (sys.reachStepk Δt η X₀ k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
