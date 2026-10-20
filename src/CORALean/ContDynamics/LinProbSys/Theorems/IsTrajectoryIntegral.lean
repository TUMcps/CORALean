module

public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryAEMeasurable

@[expose] public section

/-!
# The mean of a run

The expectation of the state of a `LinProbSys.IsTrajectory` at a time `t ≥ 0` of `T` is
`e^{At} x₀ + ∫₀ᵗ e^{A(t-s)} B u(s) ds`, the mean of the solution of [1, Eq. 2]: the mean of the
Gaussian `law` gives `x t` (`integral_id_multivariateGaussian`), read back through the image of
`P`.

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

## Hypotheses
* `traj` – probabilistic trajectory
* `ht` – `t` lies in `T`
* `h0` – time nonnegative

## Conclusion
* the expected state is the deterministic solution

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet MeasureTheory ProbabilityTheory WithLp NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `E[x(t)] = e^{At} x₀ + ∫₀ᵗ e^{A(t-s)} B u(s) ds` at every time `t ≥ 0` of `T`. -/
theorem LinProbSys.IsTrajectory.integral_eq {sys : LinProbSys n m} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {T : Set ℝ} {X₀ : S n} {U : S m} {x₀ : Vec ℝ n}
    {u : ℝ → Vec ℝ m} {x : ℝ → Ω → Vec ℝ n} (traj : sys.IsTrajectory P T X₀ U x₀ u x) {t : ℝ}
    (ht : t ∈ T) (h0 : 0 ≤ t) : -- --- CONCL ---
    ∫ ω, x t ω ∂P = exp (t • sys.A) *ᵥ x₀
      + ∫ s in (0:ℝ)..t, exp ((t - s) • sys.A) *ᵥ (sys.B *ᵥ u s) := by -- --- PROOF ---
  have hmeas := (traj.aemeasurable ht h0).1
  -- `x t` is `toLp (x t)` read back as a vector, a continuous linear equivalence
  set L := EuclideanSpace.equiv (Fin n) ℝ
  have hx : (fun ω => x t ω) = fun ω => L (toLp 2 (x t ω)) := rfl
  have hmap : ∫ ω, toLp 2 (x t ω) ∂P = ∫ y, y ∂(P.map fun ω => toLp 2 (x t ω)) :=
    (integral_map hmeas aestronglyMeasurable_id).symm
  rw [hx, L.integral_comp_comm, hmap, traj.law t ht h0, integral_id_multivariateGaussian]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
