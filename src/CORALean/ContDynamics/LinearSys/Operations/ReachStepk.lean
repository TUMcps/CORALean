import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.LinearSys.Operations.TimePoint

/-!
# One window of `reach`, enclosed from its own time point: `HR(τ_k) = HR(t_k, t_{k+1})`

CORA's `standard` scheme, its default, and [1, Alg. 4]'s recursion at a point
matrix with no input and no order reduction: the recursion runs over the
time-point sets `timePoint`, `R(t_{k+1}) = e^{AΔt} R(t_k)`, and the window
`τ_k = [k Δt, (k + 1) Δt]` is `timeIntervalStep` run once, from `R(t_k)`
directly, rather than carried step by step the way `timePoint` itself is.
Where `mtimes` only encloses, this keeps a window's own overapproximation out
of every later one, the wrapping effect `reachStepkWrappingFree` avoids the
same way, by applying `e^{A t_k}` to the first window directly rather than
`e^{AΔt}` to the window before.

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

/-- The window `τ_k = [k Δt, (k + 1) Δt]` at Taylor order `η`: `timeIntervalStep`
run once, from the time-point set `timePoint Δt X₀ k`. -/
noncomputable def LinearSys.reachStepk (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) (X₀ : S n)
    (k : ℕ) : S n :=
  sys.timeIntervalStep Δt η (sys.timePoint Δt X₀ k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
