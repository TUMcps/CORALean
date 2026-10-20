module

public import CORALean.Global.CoeffNorm

@[expose] public section

/-!
# The unit circle of an ellipsotope norm is not the ellipsotope

`[1, Prop. 2.2]` says the unit circle of `‖·‖_{E_p(G)}` coincides with `E_p(G)`. At
`G = id` on `ℝ` (any `p`, `E_p(G) = [-1, 1]`) the circle is `{-1, 1}`, which misses `0`.
The unit ball is meant (`coeffNorm_ball_eq`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the unit circle of the identity's coefficient norm differs from the image of the unit ball

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem coeffNorm_ball_eq_counterexample :
    {x : ℝ | coeffNorm (LinearMap.id : ℝ →ₗ[ℝ] ℝ) x = 1}
      ≠ (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' Metric.closedBall 0 1 := by -- --- PROOF ---
  intro h
  -- `0` lies in the ellipsotope, and its norm is `0`
  have h0 : (0 : ℝ) ∈ (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' Metric.closedBall 0 1 :=
    ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩
  rw [← h, Set.mem_setOf_eq, coeffNorm_zero] at h0
  norm_num at h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
