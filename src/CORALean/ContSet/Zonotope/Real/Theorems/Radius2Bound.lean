module

public import CORALean.ContSet.Zonotope.Real.Operations.Radius2
public import CORALean.ContSet.Interval.Real.Theorems.NormSubCenterLe
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# A zonotope lies in the ball of radius `radius₂` about its center

Each of the two radii bounds the distance `‖x - c‖₂` of a member. For the sum of generator lengths,
`x - c = ∑ βⱼ Gⱼ` with `|βⱼ| ≤ 1`, by the triangle inequality. For the box, the box of a zonotope
is centered at `c` (the half-sum of its bounds), so `Interval.norm₂_sub_center_le` applies. An
upper bound, not the smallest ball: that is a different quantity, as `radius₂`'s docstring says.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* `Z` lies in the ball of its radius around the center
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet Entrywise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Zonotope.aux_interval_center (Z : Zonotope (Vec ℝ n)) :
    Z.interval.center = Z.c := by
  funext i
  simp only [Interval.center, Zonotope.interval, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  show (2:ℝ)⁻¹ * ((Z.c i - ∑ j, |Z.G j i|) + (Z.c i + ∑ j, |Z.G j i|)) = Z.c i
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.construct_subset_ball_radius₂ (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    Z.construct ⊆ {x | ‖x - Z.c‖₂ ≤ Z.radius₂} := by -- --- PROOF ---
  intro x hx
  show ‖x - Z.c‖₂ ≤ min _ _
  refine le_min ?_ ?_
  · obtain ⟨β, hβ, rfl⟩ := hx
    rw [add_sub_cancel_left]
    refine (norm₂_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm₂_smul]
    exact mul_le_of_le_one_left (norm₂_nonneg _) (hβ j)
  · have := Interval.norm₂_sub_center_le (Z.interval_contains hx)
    rwa [Zonotope.aux_interval_center] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
