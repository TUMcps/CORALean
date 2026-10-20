module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# The covariance white noise contributes to a linear system

[1, Sec. II]: for `ẋ = Ax + u + Cξ` with white Gaussian noise `ξ`, the noise part of the state
at time `t` is Gaussian with mean `0` and covariance
`Σ_s(t) = ∫₀ᵗ e^{A(t-τ)} C Cᵀ e^{Aᵀ(t-τ)} dτ`, recalled from Gardiner's handbook. Defined here
entry by entry, as an integral of real functions, since matrices carry no norm to integrate
in by default. Only the deterministic integral is defined: the stochastic process is not.

## Inputs
* `A` – system matrix
* `C` – noise matrix
* `t` – time

## Output
* covariance matrix the white noise contributes at the time

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Σ_s(t)`, entry `(i, j)`. -/
noncomputable def noiseCovariance (A : Mat ℝ n n) (C : Mat ℝ n m) (t : ℝ) : Mat ℝ n n :=
  fun i j => ∫ τ in (0 : ℝ)..t,
    (NormedSpace.exp ((t - τ) • A) * (C * C.transpose)
      * NormedSpace.exp ((t - τ) • A.transpose)) i j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
