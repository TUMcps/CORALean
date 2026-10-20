module

public import CORALean.ContSet.ProbZonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.ProbZonotope.Real.Theorems.MapMultivariateGaussian

@[expose] public section

/-!
# `ProbZonotope.mtimes` maps the laws

Outer: the image of a law of `P` under `x ↦ Mx` is a law of `M P`: `M N(a, Σ) = N(M a, M Σ Mᵀ)`,
the means in the float zonotope image and the covariances in the interval-matrix product.

## Inputs
* `m` – natural number
* `M` – `m × n` matrix
* `P` – probabilistic zonotope

## Hypotheses
* none

## Conclusion
* the images of the laws of `P` under `M` are laws of `P.mtimes M`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open MeasureTheory ProbabilityTheory Matrix WithLp FloatOps SoundFloatArithmetic
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.mtimes_laws_outer {m : ℕ} (M : Mat 𝕋 m n) (P : ProbZonotope 𝕋 n) :
    (fun μ => μ.map (fun x => toLp 2 (toRealMat M *ᵥ ofLp x))) '' P.laws
      ⊆ (P.mtimes M).laws := by -- --- PROOF ---
  rintro _ ⟨_, ⟨a, ha, S, hS, hp, rfl⟩, rfl⟩
  -- `M` and `Mᵀ` lie in their point intervals
  have hM : toRealMat M ∈ (Interval.point M).construct := fun q => ⟨le_rfl, le_rfl⟩
  have hMt : (toRealMat M)ᵀ ∈ (Interval.point M.transpose).construct := fun q => ⟨le_rfl, le_rfl⟩
  refine ⟨toRealMat M *ᵥ a, Zonotope.mtimes_outer M P.Z ⟨a, ha, rfl⟩,
    toRealMat M * S * (toRealMat M)ᵀ,
    Interval.matMul_outer _ _ (Interval.matMul_outer _ _ hM hS) hMt, ?_, ?_⟩
  · simpa [Matrix.mul_assoc] using hp.mul_mul_conjTranspose_same (toRealMat M)
  · beta_reduce
    rw [Real.map_multivariateGaussian (toRealMat M) _ hp, WithLp.ofLp_toLp]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
