import CORALean.ContSet.Interval.Real.Theorems.NormLe
import CORALean.ContSet.Interval.Real.Theorems.IsNonempty

/-!
# `Interval.norm` is attained

On a nonempty box the corner taking, in each coordinate, the endpoint of larger magnitude is a
member whose Euclidean norm is exactly `Interval.norm`. With `Interval.norm_le` this makes
`Interval.norm` the maximum of `‖·‖₂` over the box. The nonemptiness hypothesis is needed: a crossed
box holds no point to attain it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.norm_attained {I : Interval (Vec ℝ n)} (h : I.IsNonempty) :
    ∃ x ∈ construct I, ‖x‖₂ = I.norm := by -- --- PROOF ---
  refine ⟨fun i => if |I.inf i| ≤ |I.sup i| then I.sup i else I.inf i, fun i => ?_, ?_⟩
  · have hi : I.inf i ≤ I.sup i := h i
    show I.inf i ≤ (if |I.inf i| ≤ |I.sup i| then I.sup i else I.inf i) ∧
      (if |I.inf i| ≤ |I.sup i| then I.sup i else I.inf i) ≤ I.sup i
    by_cases hc : |I.inf i| ≤ |I.sup i|
    · simpa [hc] using hi
    · simpa [hc] using hi
  · unfold Interval.norm norm₂
    refine congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => ?_)
    by_cases hc : |I.inf i| ≤ |I.sup i|
    · simp only [hc, if_true, max_eq_right hc, sq_abs]
    · simp only [hc, if_false, max_eq_left (not_le.mp hc).le, sq_abs]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
