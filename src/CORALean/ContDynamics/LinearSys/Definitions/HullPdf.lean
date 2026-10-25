module

public import CORALean.ContDynamics.LinearSys.Definitions.ClosedForm
public import CORALean.ContDynamics.LinearSys.Definitions.NoiseCovariance
public import CORALean.ContSet.ProbZonotope.Real.Definitions.GaussPdf
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The enclosing probabilistic hull of the density at time `r`

`[1, Def. 2]`, with the solutions of `[1, Eq. 1]`: `f̄_X(x, r) = sup {f_X(x, r) | X(t) a solution of
(1) on [0, r], u(t) ∈ U, f_X(x, 0) = f₀}`. With a Gaussian initial density `f₀ = N(μ₀, Σ₀)`, a
solution for an input `u` is the Gaussian of `[1, Eq. 2]`: mean `e^{rA} μ₀ + ∫₀ʳ e^{(r-τ)A} u(τ) dτ`
(`LinearSys.closedForm`) and covariance `e^{rA} Σ₀ e^{Aᵀr} + Σ_s(r)` (`noiseCovariance`), the
white noise's law taken from Eq. 2 since the stochastic process itself is not defined here.
Admissible inputs stay in `U` and are measurable, the class `LinearSys.inputReach` uses.

## Inputs
* `sys` – linear system
* `C` – noise matrix
* `U` – input set
* `μ₀` – initial mean
* `Sig₀` – initial covariance
* `r` – time
* `x` – evaluation point

## Output
* supremum of the density at the point over admissible inputs

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `f̄_X(x, r)` for the initial density `N(μ₀, Σ₀)`, the supremum over admissible inputs. -/
noncomputable def LinearSys.hullPdf (sys : LinearSys 𝕋 n) (C : Mat ℝ n m) (U : S n)
    (μ₀ : Vec ℝ n) (Sig₀ : Mat ℝ n n) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {f | ∃ u : ℝ → Vec ℝ n, (∀ s ∈ Set.Icc (0:ℝ) r, u s ∈ construct U) ∧
    AEStronglyMeasurable u (volume.restrict (Set.Icc 0 r)) ∧
    f = gaussPdf (sys.closedForm μ₀ u r) (exp (r • toRealMat sys.A) * Sig₀
      * exp (r • (toRealMat sys.A).transpose) + noiseCovariance (toRealMat sys.A) C r) x}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
