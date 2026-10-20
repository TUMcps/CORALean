module

public import CORALean.ContSet.Zonotope.Real.Definitions.MaxNormSq
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-!
# Every point is within the maximum norm

A point `c + ∑ βⱼ gⱼ` of the zonotope has `‖∑ βⱼ gⱼ‖₂² ≤ ⌈Z⌉²` [1, Def. 3]: the set the
supremum runs over is bounded by `(∑ ‖gⱼ‖₂)²`, by the triangle inequality.

## Inputs
* `Z` – zonotope
* `β` – generator coefficients

## Hypotheses
* `hβ` – coefficients within the unit box

## Conclusion
* the squared norm is at most the maximum squared norm

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.sq_norm₂_le_maxNormSq (Z : Zonotope (Vec ℝ n)) {β : Fin Z.h → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) : -- --- CONCL ---
    ‖∑ j, β j • Z.G j‖₂ ^ 2 ≤ Z.maxNormSq := by -- --- PROOF ---
  refine le_csSup ⟨(∑ j, ‖Z.G j‖₂) ^ 2, ?_⟩ ⟨β, hβ, rfl⟩
  rintro _ ⟨γ, hγ, rfl⟩
  -- the triangle inequality, each coefficient at most `1`
  have hle : ‖∑ j, γ j • Z.G j‖₂ ≤ ∑ j, ‖Z.G j‖₂ :=
    le_trans (norm₂_sum_le _ _) (Finset.sum_le_sum fun j _ => by
      rw [norm₂_smul]
      calc |γ j| * ‖Z.G j‖₂ ≤ 1 * ‖Z.G j‖₂ :=
            mul_le_mul_of_nonneg_right (hγ j) (norm₂_nonneg _)
        _ = ‖Z.G j‖₂ := one_mul _)
  exact pow_le_pow_left₀ (norm₂_nonneg _) hle 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
