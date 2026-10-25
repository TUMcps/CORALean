module

public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryAEMeasurable
public import CORALean.ContDynamics.LinearSys.Theorems.NoiseCovariancePosSemidef
public import CORALean.ContSet.ProbZonotope.Real.Theorems.ZonotopeProb
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic

@[expose] public section

/-!
# A run is in the confidence set of its probabilistic zonotope

If the mean `e^{At} x₀ + ∫₀ᵗ e^{A(t-s)} B u(s) ds` of a `LinProbSys.IsTrajectory` at a time
`t ≥ 0` of `T` lies in a zonotope `Z`, the state `x t` lies in the `γ`-confidence set
`η(𝒵, γ) = Z + (0, γ √Σ_s(t))` of the probabilistic zonotope `𝒵 = (Z, Σ_s(t))` with probability
at least `erf(γ/√2)ⁿ = P[-γ ≤ N(0, 1) ≤ γ]ⁿ`, the bound of [1, Prop. 2] and [1, Sec. V]: the law
of `x t` is one of the laws of `𝒵`, and `ProbZonotope.zonotope_prob` bounds each of them.

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
* `Z` – zonotope of means
* `γ` – confidence cut-off

## Hypotheses
* `traj` – probabilistic trajectory
* `ht` – `t` lies in `T`
* `h0` – time nonnegative
* `hZ` – the mean lies in `Z`
* `hγ` – cut-off positive

## Conclusion
* the state lies in the confidence set with at least the Gaussian probability

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet MeasureTheory ProbabilityTheory WithLp NormedSpace CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `P(x(t) ∈ η((Z, Σ_s(t)), γ)) ≥ P[-γ ≤ N(0, 1) ≤ γ]ⁿ` whenever the mean at `t` is in `Z`. -/
theorem LinProbSys.IsTrajectory.zonotope_prob {sys : LinProbSys n m} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {T : Set ℝ} {X₀ : S n} {U : S m} {x₀ : Vec ℝ n}
    {u : ℝ → Vec ℝ m} {x : ℝ → Ω → Vec ℝ n} (traj : sys.IsTrajectory P T X₀ U x₀ u x) {t : ℝ}
    (ht : t ∈ T) (h0 : 0 ≤ t) {Z : Zonotope (Vec ℝ n)}
    (hZ : exp (t • sys.A) *ᵥ x₀ + ∫ s in (0:ℝ)..t, exp ((t - s) • sys.A) *ᵥ (sys.B *ᵥ u s)
      ∈ Z.construct) {γ : ℝ} (hγ : 0 < γ) : -- --- CONCL ---
    (gaussianReal 0 1 (Set.Icc (-γ) γ)) ^ n
      ≤ P {ω | x t ω ∈ ((⟨Z, noiseCovariance sys.A sys.C t⟩ : ProbZonotope n).zonotope γ).construct}
      := by -- --- PROOF ---
  set Q : ProbZonotope n := ⟨Z, noiseCovariance sys.A sys.C t⟩
  have hmeas := (traj.aemeasurable ht h0).1
  -- the confidence set, carried to Euclidean space, is closed
  have hS : MeasurableSet (toLp 2 '' (Q.zonotope γ).construct) := by
    rw [show toLp 2 '' (Q.zonotope γ).construct = ofLp ⁻¹' (Q.zonotope γ).construct from by
      ext y; constructor
      · rintro ⟨z, hz, rfl⟩; exact hz
      · intro hy; exact ⟨ofLp y, hy, rfl⟩]
    exact (Zonotope.isClosed_construct _).measurableSet.preimage (by fun_prop)
  -- the event is the preimage of that set under `toLp (x t)`
  have hev : {ω | x t ω ∈ (Q.zonotope γ).construct}
      = (fun ω => toLp 2 (x t ω)) ⁻¹' (toLp 2 '' (Q.zonotope γ).construct) := by
    ext ω
    simp
  rw [hev, ← Measure.map_apply_of_aemeasurable hmeas hS]
  -- the law of `x t` is a law of `Q`
  exact Q.zonotope_prob (noiseCovariance_posSemidef sys.A sys.C h0) hγ ⟨_, hZ, traj.law t ht h0⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
