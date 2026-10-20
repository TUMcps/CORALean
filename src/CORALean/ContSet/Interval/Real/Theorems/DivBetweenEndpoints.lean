module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# Dividing back out of a product's endpoints

The inverse of `mul_between_endpoints`: given `lo ≤ c * x ≤ hi` for a nonzero `c`, `x`
itself sits between `lo / c` and `hi / c`, whichever way dividing by `c` swaps them.
[1, Alg. 1] uses this at each coefficient it tightens, solving a row of `A ξ = b` for `ξⱼ`
in terms of a bound already known on the rest.

## Inputs
* `c` – nonzero factor
* `lo` – lower endpoint of the product
* `hi` – upper endpoint of the product
* `x` – the quotient

## Hypotheses
* `hc` – factor nonzero
* `h₁` – lower endpoint below the product
* `h₂` – product below the upper endpoint

## Conclusion
* `x` lies between the quotients of the endpoints

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Solving a scaled point's bracket back out for the point, whichever way `c`'s sign
swaps the two endpoints. -/
theorem Interval.div_between_endpoints {c lo hi x : ℝ} (hc : c ≠ 0)
    (h₁ : lo ≤ c * x) (h₂ : c * x ≤ hi) : -- --- CONCL ---
    min (lo / c) (hi / c) ≤ x ∧ x ≤ max (lo / c) (hi / c) := by -- --- PROOF ---
  have h₁' : lo ≤ x * c := by rw [mul_comm]; exact h₁
  have h₂' : x * c ≤ hi := by rw [mul_comm]; exact h₂
  rcases lt_or_gt_of_ne hc with hc | hc
  · have hx1 : x ≤ lo / c := (le_div_iff_of_neg hc).mpr h₁'
    have hx2 : hi / c ≤ x := (div_le_iff_of_neg hc).mpr h₂'
    exact ⟨(min_le_right _ _).trans hx2, hx1.trans (le_max_left _ _)⟩
  · have hx1 : lo / c ≤ x := (div_le_iff₀ hc).mpr h₁'
    have hx2 : x ≤ hi / c := (le_div_iff₀ hc).mpr h₂'
    exact ⟨(min_le_left _ _).trans hx1, hx2.trans (le_max_right _ _)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
