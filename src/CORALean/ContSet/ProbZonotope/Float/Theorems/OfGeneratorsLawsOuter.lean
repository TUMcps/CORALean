module

public import CORALean.ContSet.ProbZonotope.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawEq

@[expose] public section

/-!
# The laws of `ofGenerators` hold those of `μ + g N`

Outer: for every mean `μ` of the zonotope, the law of `μ + g N` (`g` read as reals) is a law of
the result, whose covariance `g gᵀ` the interval-matrix product encloses.

## Inputs
* `q` – natural number
* `Z` – zonotope
* `g` – `n × q` matrix
* `μ` – mean of length `n`

## Hypotheses
* `hμ` – `μ ∈ Z.construct`

## Conclusion
* the Gaussian law with generators `g` is a law of `ofGenerators Z g`
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

theorem ProbZonotope.ofGenerators_laws_outer {q : ℕ} (Z : Zonotope (Vec 𝕋 n)) (g : Mat 𝕋 n q)
    {μ : Vec ℝ n} (hμ : μ ∈ Z.construct) :
    Real.gZonotopeLaw μ (toRealMat g) ∈ (ProbZonotope.ofGenerators Z g).laws := by
  have hg : toRealMat g ∈ (Interval.point g).construct := fun q => ⟨le_rfl, le_rfl⟩
  have hgt : (toRealMat g)ᵀ ∈ (Interval.point g.transpose).construct := fun q => ⟨le_rfl, le_rfl⟩
  exact ⟨μ, hμ, toRealMat g * (toRealMat g)ᵀ, Interval.matMul_outer _ _ hg hgt,
    by simpa using posSemidef_self_mul_conjTranspose (toRealMat g), Real.gZonotopeLaw_eq _ _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
