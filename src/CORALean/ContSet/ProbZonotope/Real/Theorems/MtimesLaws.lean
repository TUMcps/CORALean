import CORALean.ContSet.ProbZonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

/-!
# `ProbZonotope.mtimes` maps the laws

[1, Eq. 4]'s linear map: the images of the laws of `P` under `x ↦ Lx` are exactly the laws
of `L P`. The image of `N(a, Σ)` is `N(La, LΣLᵀ)`, by characteristic functions
(`⟨Lx, t⟩ = ⟨x, Lᵀt⟩`), and the means range over `L Z` (`Zonotope.mtimes_exact`). The
covariance must be positive semidefinite.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory Matrix WithLp Complex
open scoped RealInnerProductSpace

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `L N(a, Σ) = N(La, LΣLᵀ)`. -/
theorem aux_map_multivariateGaussian (M : Mat ℝ m n) (a : EuclideanSpace ℝ (Fin n))
    {S : Mat ℝ n n} (hS : S.PosSemidef) :
    (multivariateGaussian a S).map (fun x => toLp 2 (M *ᵥ ofLp x))
      = multivariateGaussian (toLp 2 (M *ᵥ ofLp a)) (M * S * Mᵀ) := by -- --- PROOF ---
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => toLp 2 (M *ᵥ ofLp x)) := by
    fun_prop
  have hMS : (M * S * Mᵀ).PosSemidef := by
    simpa [Matrix.mul_assoc] using hS.mul_mul_conjTranspose_same M
  haveI : IsProbabilityMeasure ((multivariateGaussian a S).map
      (fun x => toLp 2 (M *ᵥ ofLp x))) := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  -- `⟨Mx, t⟩ = ⟨x, Mᵀt⟩`
  have hin : ∀ (x : EuclideanSpace ℝ (Fin n)) (t : EuclideanSpace ℝ (Fin m)),
      ⟪toLp 2 (M *ᵥ ofLp x), t⟫ = ⟪x, toLp 2 (Mᵀ *ᵥ ofLp t)⟫ := by
    intro x t
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, integral_map hmeas.aemeasurable (by fun_prop)]
  simp_rw [hin]
  rw [← charFun_apply, charFun_multivariateGaussian hS, charFun_multivariateGaussian hMS]
  congr 1
  have h1 : ⟪toLp 2 (Mᵀ *ᵥ ofLp t), a⟫ = ⟪t, toLp 2 (M *ᵥ ofLp a)⟫ := by
    rw [real_inner_comm, ← hin, real_inner_comm]
  have h2 : ofLp t ⬝ᵥ (M * S * Mᵀ) *ᵥ ofLp t = (Mᵀ *ᵥ ofLp t) ⬝ᵥ S *ᵥ (Mᵀ *ᵥ ofLp t) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  rw [h1, h2]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.mtimes_laws (M : Mat ℝ m n) (P : ProbZonotope n) (h : P.cov.PosSemidef) :
    (fun μ => μ.map (fun x => toLp 2 (M *ᵥ ofLp x))) '' P.laws
      = (P.mtimes M).laws := by -- --- PROOF ---
  ext ν
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨M *ᵥ a, ?_, ?_⟩
    · rw [ProbZonotope.mtimes, ← Zonotope.mtimes_exact]
      exact ⟨a, ha, rfl⟩
    · beta_reduce
      rw [aux_map_multivariateGaussian M _ h, WithLp.ofLp_toLp]
      rfl
  · rintro ⟨μ, hμ, rfl⟩
    rw [ProbZonotope.mtimes, ← Zonotope.mtimes_exact] at hμ
    obtain ⟨a, ha, rfl⟩ := hμ
    refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
    beta_reduce
    rw [aux_map_multivariateGaussian M _ h, WithLp.ofLp_toLp]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
