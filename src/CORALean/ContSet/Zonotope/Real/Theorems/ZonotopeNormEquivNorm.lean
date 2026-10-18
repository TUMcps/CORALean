module

public import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Function

@[expose] public section

/-!
# The zonotope norm is equivalent to the others, convex, Lipschitz

`[1, Cor. 3]`: for a non-degenerate `Z`, `‖·‖_Z` is equivalent to every `p`-norm, convex,
Lipschitz-continuous and differentiable almost everywhere. Equivalence is stated against
the supremum norm (all norms on `ℝⁿ` being equivalent): above, through a continuous right
inverse of `G` (`exists_coeffNorm_le_mul_norm`); below, `‖x‖ = ‖G γ‖ ≤ ‖G‖ ‖γ‖` at a
minimizer `γ`. Convexity is the triangle inequality with homogeneity, and almost-everywhere
differentiability is Rademacher's theorem (`LipschitzWith.ae_differentiableAt`).

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zonotopeNorm_equiv_norm (Z : Zonotope (Vec ℝ n))
    (hG : Function.Surjective Z.genMap) : -- --- STMT ---
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ x, C₁ * ‖x‖ ≤ Z.zonotopeNorm x ∧ Z.zonotopeNorm x ≤ C₂ * ‖x‖) ∧
      ConvexOn ℝ Set.univ Z.zonotopeNorm ∧ (∃ K, LipschitzWith K Z.zonotopeNorm) ∧
      ∀ᵐ x ∂MeasureTheory.volume, DifferentiableAt ℝ Z.zonotopeNorm x := by -- --- PROOF ---
  obtain ⟨K, hK⟩ := exists_lipschitzWith_coeffNorm Z.genMap hG
  obtain ⟨C, hC0, hC⟩ := exists_coeffNorm_le_mul_norm Z.genMap hG
  let Gc := LinearMap.toContinuousLinearMap Z.genMap
  refine ⟨⟨1 / (‖Gc‖ + 1), C + 1, by positivity, by linarith, fun x => ⟨?_, ?_⟩⟩, ?_,
    ⟨K, hK⟩, hK.ae_differentiableAt⟩
  -- below: `‖x‖ = ‖G γ‖ ≤ ‖G‖ ν(x)` at a minimizer `γ`
  · obtain ⟨γ, hγ, hn⟩ := exists_coeffNorm_eq Z.genMap (hG x)
    have h1 : ‖x‖ ≤ ‖Gc‖ * Z.zonotopeNorm x := by
      rw [Zonotope.zonotopeNorm, ← hn, ← hγ]
      exact Gc.le_opNorm γ
    have h2 : 0 ≤ Z.zonotopeNorm x := coeffNorm_nonneg _ _
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg Gc]
  · exact (hC x).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))
  -- convexity: triangle inequality with homogeneity
  · refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
    calc Z.zonotopeNorm (a • x + b • y) ≤ Z.zonotopeNorm (a • x) + Z.zonotopeNorm (b • y) :=
          coeffNorm_add_le _ (hG _) (hG _)
      _ = a * Z.zonotopeNorm x + b * Z.zonotopeNorm y := by
          simp only [Zonotope.zonotopeNorm]
          rw [coeffNorm_smul _ (hG x), coeffNorm_smul _ (hG y), abs_of_nonneg ha,
            abs_of_nonneg hb]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
