module

public import CORALean.ContSet.Ellipsoid.Real.Operations.SupportBound
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.QMemConstruct

@[expose] public section

/-!
# The support bound is the support function

`SupportBound` claims only that nothing exceeds the value, which leaves open how
much was given away. Here nothing was: the value is a maximum, so an ellipsoid
loses no precision to the certificate machinery and a conversion read off these
bounds is as tight as the direction allows.

The attaining point is `q + G (Gᵀd)/‖Gᵀd‖₂`, the unit-ball point Cauchy–Schwarz
is tight at. When `Gᵀd` vanishes the direction is one `G` collapses, the value
is `⟨d, q⟩`, and the centre attains it — which is why the centre's membership is
what the degenerate case needs.

This is what makes [1, Def. 4] an equality here and not merely a bound; the
support vector it prints is the non-degenerate branch alone.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.supportBound_attained (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) :
    ∃ x ∈ E.construct, c x = (E.supportBound c).val := by -- --- PROOF ---
  by_cases hv : ‖E.pullback c‖₂ = 0
  · refine ⟨E.c, E.q_mem_construct, ?_⟩
    show c E.c = c E.c + ‖E.pullback c‖₂
    rw [hv, add_zero]
  · have hpos : 0 < ‖E.pullback c‖₂ := lt_of_le_of_ne (norm₂_nonneg _) (Ne.symm hv)
    refine ⟨E.c + E.G *ᵥ ((‖E.pullback c‖₂)⁻¹ • E.pullback c),
      Ellipsoid.mem_construct ?_, ?_⟩
    · rw [norm₂_smul, abs_of_nonneg (le_of_lt (inv_pos.mpr hpos)), inv_mul_cancel₀ hv]
    · show c (E.c + E.G *ᵥ ((‖E.pullback c‖₂)⁻¹ • E.pullback c))
          = c E.c + ‖E.pullback c‖₂
      rw [map_add, E.apply_mulVec c, dotProduct_smul, smul_eq_mul, dotProduct_self, pow_two,
        ← mul_assoc, inv_mul_cancel₀ hv, one_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
