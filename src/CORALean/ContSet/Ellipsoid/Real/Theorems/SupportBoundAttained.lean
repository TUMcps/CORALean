module

public import CORALean.ContSet.Ellipsoid.Real.Operations.SupportBound
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.QMemConstruct

@[expose] public section

/-!
# The support bound is the support function

`SupportBound` claims only that nothing exceeds the value, which leaves open how much was given
away. Here nothing was: the value is a maximum, so a conversion read off these bounds is as tight as
the direction allows. The value is `⟨d, q⟩ + √(dᵀ Q d) = ⟨d, q⟩ + ‖Gᵀd‖₂` (`norm₂_pullback`),
attained at `q + G (Gᵀd)/‖Gᵀd‖₂`, the unit-ball point Cauchy–Schwarz is tight at, which is CORA's `q
+ Q d/√(dᵀ Q d)`. When `Gᵀd` vanishes the direction is one `G` collapses, the value is `⟨d, q⟩`, and
the center attains it. This makes [1, Def. 4] an equality here and not merely a bound.

## Inputs
* `E` – ellipsoid
* `c` – linear functional

## Hypotheses
* none

## Conclusion
* some point of `E` attains the support bound

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.supportBound_attained (E : Ellipsoid n) (c : Vec ℝ n →ₗ[ℝ] ℝ) : -- --- CONCL ---
    ∃ x ∈ E.construct, c x = (E.supportBound c).val := by -- --- PROOF ---
  have hval : (E.supportBound c).val = c E.q + ‖E.pullback c‖₂ := by
    show c E.q + Real.sqrt _ = _
    rw [E.norm₂_pullback]
  rw [hval]
  by_cases hv : ‖E.pullback c‖₂ = 0
  · refine ⟨E.q, E.q_mem_construct, ?_⟩
    rw [hv, add_zero]
  · have hpos : 0 < ‖E.pullback c‖₂ := lt_of_le_of_ne (norm₂_nonneg _) (Ne.symm hv)
    refine ⟨E.q + E.G *ᵥ ((‖E.pullback c‖₂)⁻¹ • E.pullback c),
      Ellipsoid.mem_construct ?_, ?_⟩
    · rw [norm₂_smul, abs_of_nonneg (le_of_lt (inv_pos.mpr hpos)), inv_mul_cancel₀ hv]
    · rw [map_add, E.apply_mulVec c, dotProduct_smul, smul_eq_mul, dotProduct_self, pow_two,
        ← mul_assoc, inv_mul_cancel₀ hv, one_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
