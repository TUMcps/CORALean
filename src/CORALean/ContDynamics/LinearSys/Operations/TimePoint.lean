module

public import CORALean.ContDynamics.LinearSys.Operations.TimeInterval

@[expose] public section

/-!
# The homogeneous flow at the sample times `k Δt`, recursively

CORA's `standard` scheme, its default: the time-point set `R(t_{k+1}) = e^{AΔt}
R(t_k)` carried forward one sample at a time, `R(t_0) = X₀`. `reachStepk`
encloses each window `[k Δt, (k + 1) Δt]` from the pair of time points
`timePoint k` and `timePoint (k + 1)`'s implicit next one, which is what makes
the scheme's `timeInterval` recursion read `[1, Alg. 1]`'s own, rather than
`reachStepkWrappingFree`'s carrying the wrapped window itself forward.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `X₀` – initial set
* `k` – number of steps

## Output
* time-point set after a given number of steps

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". In Proc. of the 46th IEEE Conference on Decision and Control (CDC),
      2007, pp. 726-732.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The time-point set at `k Δt`: `R(t_0) = X₀`, `R(t_{k+1}) = e^{AΔt} R(t_k)`. -/
noncomputable def LinearSys.timePoint (sys : LinearSys 𝕋 n) (Δt : ℝ) (X₀ : S n) (k : ℕ) : S n :=
  match k with
  | 0 => X₀
  | k + 1 => Mtimes.mtimes (exp (Δt • toRealMat sys.A)) (sys.timePoint Δt X₀ k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
