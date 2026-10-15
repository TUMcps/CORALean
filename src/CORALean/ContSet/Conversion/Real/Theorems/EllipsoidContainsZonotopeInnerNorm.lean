module

public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Zonotope

@[expose] public section

/-!
# An ellipsoid as a zonotope

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: `r ≥ ⌈Z(S, 0)⌉²` puts the scaled zonotope in the ellipsoid. -/
theorem Ellipsoid.contains_zonotopeInnerNorm (E : Ellipsoid n) {m : ℕ} (S : Fin m → Vec ℝ n)
    {r : ℝ} (hr : 0 < r) (hS : (⟨m, 0, S⟩ : Zonotope (Vec ℝ n)).maxNormSq ≤ r) :
    (E.zonotopeInnerNorm S r).construct ⊆ E.construct := by -- --- PROOF ---
  rintro _ ⟨β, hβ, rfl⟩
  change ∀ j : Fin m, |β j| ≤ 1 at hβ
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  -- the coefficient point `u = r^{-1/2} ∑ βⱼ sⱼ` is in the unit ball
  have hle := le_trans (Zonotope.sq_norm₂_le_maxNormSq ⟨m, 0, S⟩ hβ) hS
  refine ⟨(√r)⁻¹ • ∑ j, β j • S j, ?_, ?_⟩
  · rw [norm₂_smul, abs_of_pos (inv_pos.mpr hs), inv_mul_le_iff₀ hs, mul_one]
    calc ‖∑ j, β j • S j‖₂ = √(‖∑ j, β j • S j‖₂ ^ 2) := (Real.sqrt_sq (norm₂_nonneg _)).symm
      _ ≤ √r := Real.sqrt_le_sqrt hle
  · show E.q + ∑ j, β j • ((√r)⁻¹ • (E.G *ᵥ S j)) = E.q + E.G *ᵥ ((√r)⁻¹ • ∑ j, β j • S j)
    rw [Matrix.mulVec_smul, Matrix.mulVec_sum, Finset.smul_sum]
    simp only [Matrix.mulVec_smul, smul_comm (√r)⁻¹]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
