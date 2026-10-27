module

public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryAEMeasurable
public import CORALean.ContDynamics.LinearSys.Theorems.NoiseCovariancePosSemidef

@[expose] public section

/-!
# The covariance of a run

The covariance of two coordinates of the state of a `LinProbSys.IsTrajectory` at a time `t ≥ 0`
of `T` is the entry of `Σ_s(t) = ∫₀ᵗ e^{A(t-τ)} C Cᵀ e^{Aᵀ(t-τ)} dτ` (`noiseCovariance`), the
covariance of the solution of [1, Eq. 2]: `Σ_s(t)` is positive semidefinite
(`noiseCovariance_posSemidef`), so it is the covariance of the Gaussian `law` gives `x t`
(`covariance_eval_multivariateGaussian`), read back through the image of `P`.

## Inputs
* `sys` – system
* `Ω` – sample space
* `P` – probability measure
* `T` – time set
* `X₀` – initial set
* `U` – input set
* `x₀` – initial state
* `u` – input signal
* `x` – state process
* `t` – time
* `i` – first coordinate
* `j` – second coordinate

## Hypotheses
* `traj` – probabilistic trajectory
* `ht` – `t` lies in `T`
* `h0` – time nonnegative

## Conclusion
* the covariance of two state coordinates is the noise covariance entry

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.](../../../../../references/2009/althoff-ecc-enclosing-hulls.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet MeasureTheory ProbabilityTheory WithLp

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `cov[x_i(t), x_j(t)] = Σ_s(t)_ij` at every time `t ≥ 0` of `T`. -/
theorem LinProbSys.IsTrajectory.covariance_eq {sys : LinProbSys n m} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {T : Set ℝ} {X₀ : S n} {U : S m} {x₀ : Vec ℝ n}
    {u : ℝ → Vec ℝ m} {x : ℝ → Ω → Vec ℝ n} (traj : sys.IsTrajectory P T X₀ U x₀ u x) {t : ℝ}
    (ht : t ∈ T) (h0 : 0 ≤ t) (i j : Fin n) : -- --- CONCL ---
    cov[fun ω => x t ω i, fun ω => x t ω j; P]
      = noiseCovariance sys.A sys.C t i j := by -- --- PROOF ---
  have hmeas := (traj.aemeasurable ht h0).1
  have hcoord : ∀ k : Fin n, AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) => y k)
      (P.map fun ω => toLp 2 (x t ω)) := fun k =>
    (Continuous.aestronglyMeasurable (by fun_prop))
  -- the coordinates of `x t` are those of `toLp (x t)`, under the image of `P`
  have h := covariance_map_fun (hcoord i) (hcoord j) hmeas
  rw [traj.law t ht h0,
    covariance_eval_multivariateGaussian (noiseCovariance_posSemidef sys.A sys.C h0)] at h
  exact h.symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
