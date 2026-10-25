module

public import CORALean.ContDynamics.LinearSys.Definitions.InputLaws
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq
public import CORALean.ContDynamics.LinearSys.Theorems.NoiseCovariancePosSemidef
public import CORALean.ContDynamics.LinProbSys.Theorems.NoiseCovarianceAdd
public import CORALean.ContSet.ProbZonotope.Real.Theorems.ConvMultivariateGaussian
public import CORALean.ContSet.ProbZonotope.Real.Theorems.MapMultivariateGaussian

@[expose] public section

/-!
# The input solution's laws split at any intermediate time

`[1, Prop. 4]` at a time point, the decomposition of its proof
`x_s(a + b) = e^{Ab} x_s(a) + x_s'(b)`: the laws of the input solution at `a + b` are exactly the
laws of `e^{Ab} X + Y`, `X` a law at `a` and `Y` an independent law at `b`, the convolution of
the image of `X` under `e^{Ab}` with `Y`. The means are `LinearSys.inputReach_separation_eq`
(the thesis' Prop. 3.2), the covariances `noiseCovariance_add`; the Gaussians are mapped and
added by `map_multivariateGaussian` and `conv_multivariateGaussian`, for positive semidefinite
covariances. The input set is bounded, which makes every admissible input integrable.

## Inputs
* `sys` – linear system
* `C` – noise matrix
* `U` – input set
* `a` – first time
* `b` – second time

## Hypotheses
* `ha` – first time nonnegative
* `hb` – second time nonnegative
* `hbdd` – input set bounded

## Conclusion
* the laws at the summed time are convolutions of the laws at each time

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

open Matrix ContSet Scalar NormedSpace MeasureTheory ProbabilityTheory WithLp Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.inputLaws_add (sys : LinearSys 𝕋 n) (C : Mat ℝ n m) {U : S n} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbdd : Bornology.IsBounded (construct U)) : -- --- CONCL ---
    sys.inputLaws C U (a + b)
      = {ν | ∃ ν₁ ∈ sys.inputLaws C U a, ∃ ν₂ ∈ sys.inputLaws C U b,
          ν = (ν₁.map fun x => toLp 2 (exp (b • toRealMat sys.A) *ᵥ ofLp x))
            ∗ ν₂} := by -- --- PROOF ---
  -- the covariances
  set A := toRealMat sys.A with hA
  set E := exp (b • A) with hE
  have hET : Eᵀ = exp (b • A.transpose) := by
    rw [hE, ← Matrix.exp_transpose, Matrix.transpose_smul]
  have hcov : noiseCovariance A C (a + b)
      = E * noiseCovariance A C a * Eᵀ + noiseCovariance A C b := by
    rw [add_comm, noiseCovariance_add, hET]
  have hPa := noiseCovariance_posSemidef A C ha
  have hPb := noiseCovariance_posSemidef A C hb
  have hPE : (E * noiseCovariance A C a * Eᵀ).PosSemidef := by
    simpa [Matrix.mul_assoc] using hPa.mul_mul_conjTranspose_same E
  -- the image and the sum of two such laws
  have hlaw : ∀ y₁ y₂ : Vec ℝ n,
      ((multivariateGaussian (toLp 2 y₁) (noiseCovariance A C a)).map
          fun x => toLp 2 (E *ᵥ ofLp x)) ∗ multivariateGaussian (toLp 2 y₂) (noiseCovariance A C b)
        = multivariateGaussian (toLp 2 (E *ᵥ y₁ + y₂)) (noiseCovariance A C (a + b)) := by
    intro y₁ y₂
    rw [Real.map_multivariateGaussian E _ hPa, Real.conv_multivariateGaussian _ _ hPE hPb, hcov]
    rfl
  ext ν
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [LinearSys.inputReach_separation_eq sys ha hb hbdd] at hy
    obtain ⟨_, ⟨y₁, hy₁, rfl⟩, y₂, hy₂, rfl⟩ := hy
    exact ⟨_, ⟨y₁, hy₁, rfl⟩, _, ⟨y₂, hy₂, rfl⟩, (hlaw y₁ y₂).symm⟩
  · rintro ⟨_, ⟨y₁, hy₁, rfl⟩, _, ⟨y₂, hy₂, rfl⟩, rfl⟩
    refine ⟨E *ᵥ y₁ + y₂, ?_, (hlaw y₁ y₂).symm ▸ rfl⟩
    rw [LinearSys.inputReach_separation_eq sys ha hb hbdd]
    exact ⟨_, ⟨y₁, hy₁, rfl⟩, y₂, hy₂, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
