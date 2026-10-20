module

public import CORALean.ContSet.Taylm.Real.Operations.QfbSearchStep
public import CORALean.ContSet.Taylm.Real.Taylm
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The search step is the projection onto the box

[1, Sec. 3 (search for x₀)]'s search limits each `x₀⁽ⁱ⁾` to `D`. Limiting the gradient step
`y = x - α∇P₂(x)` coordinate by coordinate to `[-1, 1]` is the nearest point of the box, and that is
what the analysis of the search uses: the result lies in the box, and `(y - x⁺) ⬝ (z - x⁺) ≤ 0` for
every `z` in the box. Coordinate by coordinate, either `y_k` is inside and the factor is `0`, or it
was cut at `±1` and `z_k` lies on the other side of the cut.

## Inputs
* `H` – Hessian matrix
* `g` – gradient
* `α` – step length
* `x` – point

## Hypotheses
* none

## Conclusion
* the step stays in the unit box and is the projection of the gradient step

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3 (search for x₀)]: the step stays in the box and is the projection of `x - α∇P₂(x)`
onto it. -/
theorem Taylm.qfbSearchStep_variational (H : Mat ℝ n n) (g : Vec ℝ n) (α : ℝ) (x : Vec ℝ n) :
    Taylm.qfbSearchStep H g α x ∈ Taylm.box n ∧
      ∀ z ∈ Taylm.box n, (x - α • (g + H *ᵥ x) - Taylm.qfbSearchStep H g α x)
        ⬝ᵥ (z - Taylm.qfbSearchStep H g α x) ≤ 0 := by -- --- PROOF ---
  refine ⟨fun k => abs_le.mpr ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩,
    fun z hz => Finset.sum_nonpos fun k _ => ?_⟩
  -- one coordinate: `y` cut at `±1`, or left alone
  show ((x - α • (g + H *ᵥ x)) k - max (-1) (min 1 ((x - α • (g + H *ᵥ x)) k)))
      * (z k - max (-1) (min 1 ((x - α • (g + H *ᵥ x)) k))) ≤ 0
  set y := (x - α • (g + H *ᵥ x)) k
  obtain ⟨hz1, hz2⟩ := abs_le.mp (hz k)
  rcases le_total y 1 with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-1) y with h2 | h2
    · rw [max_eq_right h2, sub_self, zero_mul]
    · rw [max_eq_left h2]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  · rw [min_eq_left h1, max_eq_right (by norm_num)]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
