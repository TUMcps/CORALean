module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# [1, Eq. 7] as printed under-estimates the probability

Take the one-dimensional state `X ~ N(0, σ²)`, `σ = 1/100` — a G-zonotope `(0, σ)` with certain
mean, its own enclosing probabilistic hull — the confidence set `η = [-3σ, 3σ]` (`γ = 3`), and
the unsafe set `B = η`. Then `erf(γ/√2) = P[|N(0, 1)| ≤ 3] = P(X ∈ B) =: p`, and however the
confidence rings `Qᵢ` partition `η`, `Σᵢ V(Qᵢ ∩ B) = V(B) = 6σ`. [1, Eq. 7] prints
`p̄ = 1 - p^{2n} + Σᵢ V(Qᵢ ∩ B) = 1 - p² + 0.06`, while `P(X ∈ B) = p ≥ 8/9` by Chebyshev's
inequality, and `1 - p² + 0.06 < p` there: the printed `p̄` is no upper bound. The volumes need
the hull's heights `hᵢ^max` as factors (`UnsafeProbLe`).

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

open MeasureTheory ProbabilityTheory


-- =======================================  MAIN THEOREM  ======================================= --

theorem unsafe_prob_printed_counterexample :
    let ν := gaussianReal 0 (1 / 10000)
    let B := Set.Icc (-(3 / 100) : ℝ) (3 / 100)
    1 - (ν B).toReal ^ 2 + volume.real B < (ν B).toReal := by -- --- PROOF ---
  intro ν B
  have hB : MeasurableSet B := measurableSet_Icc
  -- Chebyshev: `P(|X| ≥ 3σ) ≤ σ²/(3σ)² = 1/9`
  have hcheb := meas_ge_le_variance_div_sq (μ := ν) (memLp_id_gaussianReal 2)
    (by norm_num : (0 : ℝ) < 3 / 100)
  have hmean : ν[id] = 0 := integral_id_gaussianReal
  have hvar : variance id ν = 1 / 10000 := by
    rw [variance_id_gaussianReal]; norm_num
  rw [hmean, hvar] at hcheb
  have hsub : Bᶜ ⊆ {ω | 3 / 100 ≤ |id ω - 0|} := by
    intro x hx
    simp only [B, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    simp only [Set.mem_setOf_eq, id, sub_zero]
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hc : (ν Bᶜ).toReal ≤ 1 / 9 := by
    have := (measure_mono hsub).trans hcheb
    have h9 : ENNReal.ofReal (1 / 10000 / (3 / 100) ^ 2) = ENNReal.ofReal (1 / 9) := by norm_num
    rw [h9] at this
    calc (ν Bᶜ).toReal ≤ (ENNReal.ofReal (1 / 9)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top this
      _ = 1 / 9 := ENNReal.toReal_ofReal (by norm_num)
  -- `p = P(X ∈ B) ≥ 8/9`
  have hsum : (ν B).toReal + (ν Bᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl hB, measure_univ, ENNReal.toReal_one]
  have hp1 : (ν B).toReal ≤ 1 := by
    have := ENNReal.toReal_nonneg (a := ν Bᶜ); linarith
  have hp : 8 / 9 ≤ (ν B).toReal := by linarith
  have hV : volume.real B = 6 / 100 := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]; norm_num
  rw [hV]
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
