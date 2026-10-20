module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Zonotope
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawEq
public import CORALean.ContSet.ProbZonotope.Real.Theorems.StdGaussianBox
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# Every law of a probabilistic zonotope puts `erf(m/√2)ⁿ` on its confidence set

[1, Prop. 2] extended to an uncertain mean, as [1, Sec. V] uses it: whatever the mean `μ ∈ Z`,
the realizations of `N(μ, Σ)` lie in `η(𝒵, m) = Z + (0, m g)` with probability at least
`erf(m/√2)ⁿ = P[-m ≤ N(0, 1) ≤ m]ⁿ`, so the complement `Ψ` carries at most `1 - erf(m/√2)ⁿ`.
`N(μ, Σ)` is the law of `μ + gN` with `g` the square root of `Σ` (`gZonotopeLaw_eq`), and
`μ + gβ` is in the set whenever `β` is in the cube `[-m, m]ⁿ`. The covariance must be positive
semidefinite and `m > 0`.

## Inputs
* `P` – probabilistic zonotope
* `m` – real number
* `ν` – measure

## Hypotheses
* `hP` – `P.cov` is positive semidefinite
* `hm` – `0 < m`
* `hν` – `ν ∈ P.laws`

## Conclusion
* every law of a probabilistic zonotope puts `erf(m/√2)ⁿ` on its confidence set

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
namespace CORALean.Real

open MeasureTheory ProbabilityTheory WithLp Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.zonotope_prob (P : ProbZonotope n) (hP : P.cov.PosSemidef) {m : ℝ}
    (hm : 0 < m) {ν : Measure (EuclideanSpace ℝ (Fin n))} (hν : ν ∈ P.laws) : -- --- CONCL ---
    (gaussianReal 0 1 (Set.Icc (-m) m)) ^ n
      ≤ ν (toLp 2 '' (P.zonotope m).construct) := by -- --- PROOF ---
  obtain ⟨μ, hμ, rfl⟩ := hν
  set B := CFC.sqrt P.cov
  have hBB : B * B = P.cov := CFC.sqrt_mul_sqrt_self P.cov hP.nonneg
  have hBt : Bᵀ = B := by
    have := (CFC.sqrt_nonneg P.cov).isSelfAdjoint
    simpa [IsSelfAdjoint, star_eq_conjTranspose] using this
  -- `N(μ, Σ)` is the law of `μ + B N`
  have hlaw : multivariateGaussian (toLp 2 μ) P.cov = gZonotopeLaw μ B := by
    rw [gZonotopeLaw_eq, hBt, hBB]
  rw [hlaw, ← stdGaussian_cube m, gZonotopeLaw]
  refine le_trans (measure_mono ?_) (Measure.le_map_apply (by fun_prop) _)
  -- the cube lands in the confidence set
  intro β hβ
  refine ⟨μ + B *ᵥ ofLp β, ?_, rfl⟩
  rw [ProbZonotope.zonotope, ← Zonotope.plus_exact]
  refine Set.add_mem_add hμ ⟨fun j => ofLp β j / m, fun j => ?_, ?_⟩
  · rw [abs_div, abs_of_pos hm, div_le_one hm]
    exact abs_le.2 (hβ j)
  · funext i
    simp only [confidenceZonotope, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    change B i j * ofLp β j = ofLp β j / m * (m * B i j)
    field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
