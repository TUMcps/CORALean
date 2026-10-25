module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceLineCl

@[expose] public section

/-!
# `Zonotope.reduceLineCl` bounds the generator count

`reduceByBasis` appends one generator per axis, as `reduceBy` does, so the count is
`(o - 1) * n + n = o * n` above the order and unchanged at or below it, the bound
of `reducePCA_order_le`, here for [1, Alg. 3]. At `o = 0` there is nothing to state.

## Inputs
* `Z` – zonotope
* `o` – target order
* `ξ` – convergence threshold
* `fuel` – iteration budget
* `runs` – number of restarts

## Hypotheses
* `ho` – order positive

## Conclusion
* the result has at most `o n` generators

## References

* [1] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of Zonotopes". 2017
      IEEE 56th Annual Conference on Decision and Control (CDC), 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceLineCl_order_le (Z : Zonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o) (ξ : ℝ)
    (fuel runs : ℕ) : -- --- CONCL ---
    (Z.reduceLineCl o ξ fuel runs).h ≤ o * n := by -- --- PROOF ---
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold Zonotope.reduceLineCl
  split_ifs with hlt
  · exact le_of_eq hK
  · exact Nat.le_of_not_lt hlt


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
