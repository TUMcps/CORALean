module

public import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawEq
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawEqWithDensity
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# The density of a G-zonotope with certain mean

[1, Prop. 1], corrected: if `Σ = G Gᵀ` is invertible, the law of `c + G N` has the density
`(2π)^{-n/2} det(Σ)^{-1/2} exp(-½ (x - c)ᵀ Σ⁻¹ (x - c))` on `ℝⁿ`. [1] prints `(2π)^{-q/2}`, the
normalization of the `q` independent generators' joint density, which is not one of `x ∈ ℝⁿ`
when `q > n` (`GZonotopeLawPrintedPdf`). And [1]'s hypothesis "order greater than
one (`q > n`)" does not make `Σ` invertible — `G` needs rank `n`, which `det Σ ≠ 0` states;
`q = n` with `G` invertible is allowed too. The proof goes through the square root `B` of `Σ`:
`c + G N` and `c + B N` have the same law (`gZonotopeLaw_eq`), and `B` is square and
invertible (`gZonotopeLaw_eq_withDensity`).

## Inputs
* `c` – center of length `n`
* `G` – `n × q` matrix

## Hypotheses
* `hG` – `G Gᵀ` is invertible

## Conclusion
* the law has the Gaussian density with mean `c` and covariance `G Gᵀ`

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder

variable {n q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem gZonotopeLaw_eq_withDensity_gaussPdf (c : Vec ℝ n) (G : Mat ℝ n q)
    (hG : (G * Gᵀ).det ≠ 0) : -- --- CONCL ---
    gZonotopeLaw c G
      = volume.withDensity (fun x => ENNReal.ofReal (gaussPdf c (G * Gᵀ) x)) := by -- --- PROOF ---
  set S := G * Gᵀ with hSdef
  have hS : S.PosSemidef := by simpa using posSemidef_self_mul_conjTranspose G
  -- the symmetric square root `B` of `Σ`
  set B := CFC.sqrt S with hBdef
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hBt : Bᵀ = B := by
    have := (CFC.sqrt_nonneg S).isSelfAdjoint
    simpa [IsSelfAdjoint, star_eq_conjTranspose] using this
  have hdet : B.det ^ 2 = S.det := by rw [sq, ← det_mul, hBB]
  have hB : B.det ≠ 0 := by
    intro h; apply hG; rw [← hdet, h]; ring
  have hlaw : gZonotopeLaw c G = gZonotopeLaw c B := by
    rw [gZonotopeLaw_eq, gZonotopeLaw_eq, hBt, hBB]
  rw [hlaw, gZonotopeLaw_eq_withDensity c B hB]
  congr 1
  funext x
  congr 1
  -- `‖B⁻¹(x - c)‖² = (x - c)ᵀ Σ⁻¹ (x - c)` and `|det B|⁻¹ = det(Σ)^{-1/2}`
  set v := ofLp x - c with hv
  have hBinvT : (B⁻¹)ᵀ = B⁻¹ := by rw [transpose_nonsing_inv, hBt]
  have hnorm : ‖toLp 2 (B⁻¹ *ᵥ v)‖ ^ 2 = v ⬝ᵥ S⁻¹ *ᵥ v := by
    rw [EuclideanSpace.real_norm_sq_eq, ← hBB, Matrix.mul_inv_rev, ← mulVec_mulVec,
      dotProduct_mulVec, ← mulVec_transpose, hBinvT]
    simp [dotProduct, sq]
  have hpow : S.det ^ (-(1 : ℝ) / 2) = |B.det|⁻¹ := by
    rw [← hdet, ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
    exact Real.rpow_neg_one _
  simp only [stdGaussPdf, gaussPdf, hpow, neg_dotProduct]
  rw [hnorm, ← hv]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
