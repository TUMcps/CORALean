module

public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Definitions.NoiseCovariance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
# The laws of the input solution at time `t`

`[1, Prop. 4]` (with `[1, Eq. 1]`, `[1, Sec. IV]`): the input solution
`x_s(t) = ∫₀ᵗ e^{A(t-τ)} v(τ) dτ` for `v = u + Cξ` is, for each admissible `u`, the Gaussian with
mean `∫₀ᵗ e^{A(t-τ)} u(τ) dτ` and covariance `Σ_s(t)` (`[1, Eq. 2]`). The family over all `u` is
`R̄(t)`, the G-zonotope with uncertain mean `(R̄(t), Σ_s(t))` read as the set of its laws: the
means are `LinearSys.inputReach`, the covariance `noiseCovariance`.

## Inputs
* `sys` – linear system
* `C` – noise matrix
* `U` – input set
* `t` – time

## Output
* set of Gaussian laws of the input solution at the time

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar MeasureTheory ProbabilityTheory WithLp

variable {n m : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Gaussians `N(y, Σ_s(t))` with `y` a point the input reaches at time `t`. -/
noncomputable def LinearSys.inputLaws (sys : LinearSys 𝕋 n) (C : Mat ℝ n m) (U : S n) (t : ℝ) :
    Set (Measure (EuclideanSpace ℝ (Fin n))) :=
  {ν | ∃ y ∈ sys.inputReach U t,
    ν = multivariateGaussian (toLp 2 y) (noiseCovariance (toRealMat sys.A) C t)}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
