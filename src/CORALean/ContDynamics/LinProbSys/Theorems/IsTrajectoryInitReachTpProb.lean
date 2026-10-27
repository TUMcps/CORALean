module

public import CORALean.ContDynamics.LinProbSys.Theorems.InputCovEq
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryMeanSplit
public import CORALean.ContDynamics.LinProbSys.Theorems.IsTrajectoryZonotopeProb
public import CORALean.ContDynamics.LinProbSys.Operations.InitReach
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulExpIntegral
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem

@[expose] public section

/-!
# A run is in the time-point set of `initReach` with the claimed confidence

For every `LinProbSys.IsTrajectory` from a point of `Rinit`'s zonotope of means under inputs in
CORA's `U + uTrans` [1], on a `T` that holds the first step `[0, r]`, the state at `r` lies in
the set of `Rfirst.tp = eAt Rinit + zonotope(Rpar)` with probability at least
`P[-γ ≤ N(0, 1) ≤ γ]ⁿ`, `γ = gamma`: the bound [2, Prop. 2] and [2, Sec. V] give the
`γ`-confidence set of a G-zonotope with uncertain mean. The set is `η(𝒵, γ)` for
`𝒵 = (eAt Rinit + Rinput, Σ)`, `Σ` the input covariance of `initReach`, which is `Σ_s(r)`
(`inputCov_eq_noiseCovariance`); the run's mean is in `eAt Rinit + Rinput` (`initReach_tp_outer`)
and `IsTrajectory.zonotope_prob` bounds the probability. Asked: `initReach_tp_outer`'s, and `γ > 0`.

## Inputs
* `sys` – system
* `Veig` – eigenvector matrix
* `lambda` – eigenvalues
* `Rinit` – initial probabilistic zonotope
* `gammaInit` – confidence level of the initial set
* `U` – input zonotope
* `uTrans` – constant input
* `r` – step size
* `η` – Taylor order
* `gamma` – confidence level
* `originContained` – input set holds the origin
* `Ω` – sample space
* `P` – probability measure
* `T` – time set
* `x₀` – initial state
* `u` – input signal
* `x` – state process

## Hypotheses
* `hV` – eigenvector matrix invertible
* `hAV` – `Veig` and `lambda` diagonalize the matrix
* `hr` – step positive
* `hε` – order admissible
* `hγ` – confidence level positive
* `hA` – matrix invertible
* `traj` – probabilistic trajectory
* `hT` – first step lies in the time set

## Conclusion
* the state at `r` lies in the time-point set with the Gaussian probability

## References

* [1] `contDynamics/@linProbSys/initReach.m`
* [2] [M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.](../../../../../references/2009/althoff-ecc-enclosing-hulls.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix MeasureTheory ProbabilityTheory NormedSpace
open scoped Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `P(x(r) ∈ Rfirst.tp) ≥ P[-γ ≤ N(0, 1) ≤ γ]ⁿ` for every run from `Rinit` under inputs in
`U + uTrans`. -/
theorem LinProbSys.IsTrajectory.initReach_tp_prob (sys : LinProbSys n m) (Veig : Mat ℝ n n)
    (lambda : Fin n → ℝ) (hV : IsUnit Veig.det) (hAV : sys.A = Veig * diagonal lambda * Veig⁻¹)
    (Rinit : ProbZonotope n) (gammaInit : ℝ) (U : Zonotope (Vec ℝ m)) (uTrans : Vec ℝ m)
    {r : ℝ} (hr : 0 < r) {η : ℕ} (hε : ‖r • sys.A‖ / ((η : ℝ) + 2) < 1) {gamma : ℝ}
    (hγ : 0 < gamma) (originContained : Bool) (hA : IsUnit sys.A.det) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {T : Set ℝ} {x₀ : Vec ℝ n} {u : ℝ → Vec ℝ m}
    {x : ℝ → Ω → Vec ℝ n}
    (traj : sys.IsTrajectory (S := 𝒵) P T Rinit.Z (U.plus (Zonotope.ofPoint uTrans)) x₀ u x)
    (hT : Set.Icc 0 r ⊆ T) : -- --- CONCL ---
    (gaussianReal 0 1 (Set.Icc (-gamma) gamma)) ^ n
      ≤ P {ω | x r ω ∈ (sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma
          originContained).1.Z.construct} := by -- --- PROOF ---
  set A := sys.A with hAdef
  set v := sys.B *ᵥ uTrans with hv
  set Rtrans := (A⁻¹ * (exp (r • A) - 1)) *ᵥ v with hRtrans
  set inputSolV := (LinearSys.canonical A : LinearSys ℝ n).inputSolution (S := 𝒵) r η
    (Zonotope.mtimes sys.B U) with hinputSolV
  -- the means `eAt Rinit + Rinput`
  set Zm : Zonotope (Vec ℝ n) := (Zonotope.mtimes (exp (r • A)) Rinit.Z).plus
    ((inputSolV.plus (Zonotope.ofPoint Rtrans)).plus (Zonotope.ofPoint 0)) with hZm
  -- the mean of the run is one of them
  have hmean : exp (r • A) *ᵥ x₀ + ∫ s in (0:ℝ)..r, exp ((r - s) • A) *ᵥ (sys.B *ᵥ u s)
      ∈ Zm.construct := by
    obtain ⟨w, hw, heq⟩ := traj.mean_eq_add_inputReach hr.le hT
    rw [heq]
    have h1 : exp (r • A) *ᵥ x₀ ∈ (Zonotope.mtimes (exp (r • A)) Rinit.Z).construct := by
      rw [← Zonotope.mtimes_exact]
      exact Set.mem_image_of_mem _ traj.init
    have hw' : w ∈ inputSolV.construct :=
      LinearSys.inputReach_subset_inputSolution (S := 𝒵) (LinearSys.canonical A) hr η
      hε (Zonotope.convex_construct _) (Zonotope.isClosed_construct _)
      (Zonotope.isCompact_construct _).isBounded (Zonotope.convex_construct _)
      (Zonotope.isClosed_construct _) (Zonotope.isCompact_construct _).isBounded hw
    -- `w + Rtrans + 0` in `Rinput`, `eAt x₀` beside it
    have h5 := Set.add_mem_add (Set.add_mem_add hw' (Zonotope.mem_ofPoint Rtrans))
      (Zonotope.mem_ofPoint (0 : Vec ℝ n))
    rw [Zonotope.plus_exact, Zonotope.plus_exact] at h5
    have hall := Set.add_mem_add h1 h5
    rw [Zonotope.plus_exact] at hall
    -- `∫₀ʳ e^{Aσ} dσ B uTrans` is `Rtrans`, the rest is `eAt x₀` and `w`
    have hsum : exp (r • A) *ᵥ x₀ + MatExp.expIntegral A r *ᵥ v + w
        = exp (r • A) *ᵥ x₀ + (w + Rtrans + 0) := by
      rw [MatExp.expIntegral_eq_inv_mul A hA r, hRtrans]
      abel
    rw [hsum]
    exact hall
  -- the confidence set of `(Zm, Σ_s(r))` is the time-point set
  have hsub : ((⟨Zm, noiseCovariance A sys.C r⟩ : ProbZonotope n).zonotope gamma).construct
      ⊆ (sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma
          originContained).1.Z.construct := by
    have hcov : (0 : Mat ℝ n n) + LinProbSys.inputCov Veig lambda sys.C r
        = noiseCovariance A sys.C r := by
      rw [zero_add, LinProbSys.inputCov_eq_noiseCovariance A Veig lambda hV hAV]
    simp only [hZm, LinProbSys.initReach, ProbZonotope.plus, ProbZonotope.mtimes,
      ProbZonotope.zonotope, hcov]
    simp only [← Zonotope.plus_exact]
    exact (add_assoc (_ : Set (Vec ℝ n)) _ _).subset
  exact (traj.zonotope_prob (hT ⟨hr.le, le_rfl⟩) hr.le hmean hγ).trans
    (measure_mono fun ω hω => hsub hω)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
