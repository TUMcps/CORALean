module

public import CORALean.ContDynamics.LinearSys.Definitions.NoiseCovariance
public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
# Linear systems with white noise: the representation

CORA's `linProbSys` [1], the multivariate Ornstein-Uhlenbeck process
`ẋ = A x + B u + C ξ` with white Gaussian noise `ξ`, [3, Eq. 1] with its input through `B`.
Real layer only: the noise is a Gaussian process, with no float counterpart. `C` is square, as
CORA's `inputArgsCheck` asks.

`IsTrajectory` is a run, given by its law: a process `x` on `(Ω, P)`, from a point `x₀ ∈ X₀`
(as `simulate` [2] starts) under a measurable input `u` in `U`, whose state at every `t ≥ 0` of
`T` has the law `N(e^{At} x₀ + ∫₀ᵗ e^{A(t-s)} B u(s) ds, noiseCovariance A C t)`: [3, Eq. 2],
the law of `x(t) = e^{At} x₀ + ∫₀ᵗ e^{A(t-s)} B u(s) ds + ∫₀ᵗ e^{A(t-s)} C dW(s)`, restated there
from Gardiner's handbook. It is the definition, not a theorem: Mathlib's Brownian motion
(`IsBrownianReal`) comes with neither existence nor a stochastic integral, so the solution
driven by a Brownian `W` is not defined and its law is not derived. Only the law at each time
is fixed, not the joint law of two times; a reach set at a time point asks no more.

## References

* [1] `contDynamics/@linProbSys/linProbSys.m`
* [2] `contDynamics/@linProbSys/simulate.m`
* [3] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet MeasureTheory ProbabilityTheory WithLp NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- `ẋ = A x + B u + C ξ` [3, Eq. 1]: the three matrices, `n` states and `m` inputs. -/
structure LinProbSys (n m : ℕ) where
  A : Mat ℝ n n
  B : Mat ℝ n m
  C : Mat ℝ n n

/-- A run on `T` from `x₀ ∈ X₀` under `u` in `U`, by its law: at every `t ≥ 0` of `T`, `x t` is
distributed as `N(e^{At} x₀ + ∫₀ᵗ e^{A(t-s)} B u(s) ds, Σ_s(t))`, the solution's [3, Eq. 2]. -/
structure LinProbSys.IsTrajectory (sys : LinProbSys n m) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : Set ℝ) (X₀ : S n) (U : S m) (x₀ : Vec ℝ n) (u : ℝ → Vec ℝ m)
    (x : ℝ → Ω → Vec ℝ n) : Prop where
  init : x₀ ∈ construct X₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  meas : AEStronglyMeasurable u (volume.restrict T)
  law (t : ℝ) (ht : t ∈ T) (h0 : 0 ≤ t) :
    P.map (fun ω => toLp 2 (x t ω))
      = multivariateGaussian
          (toLp 2 (exp (t • sys.A) *ᵥ x₀
            + ∫ s in (0:ℝ)..t, exp ((t - s) • sys.A) *ᵥ (sys.B *ᵥ u s)))
          (noiseCovariance sys.A sys.C t)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
