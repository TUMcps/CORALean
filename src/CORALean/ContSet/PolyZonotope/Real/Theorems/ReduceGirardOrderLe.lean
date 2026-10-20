module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce

@[expose] public section

/-!
# Girard's reduction bounds the generator count

`reduceGirard o` returns at most `o·n` generators, dependent and independent together.
Counting the two blocks together makes that true, and separates this from
`reduceGirardDependent`, where each call adds `n` independent generators and removes none. The
proof is arithmetic: both budgets are clamped, to their block and to `K = (o-1)·n` between
them, so it never appeals to the ranking, which stays a heuristic. At `o = 0` there is nothing
to state: CORA floors the budget at nothing and adds the box of `n` regardless.

## Inputs
* `pZ` – polynomial zonotope
* `o` – target order

## Hypotheses
* `ho` – order is positive

## Conclusion
* the generator count is at most the order times the dimension
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The count arithmetic, and all of it: two budgets summing to at most `K`,
each clamped to the block it cuts, plus the `m` the box adds. -/
theorem PolyZonotope.aux_order_arith {d K h q m : ℕ} (hd : d ≤ K) :
    min d h + (min (K - d) q + m) ≤ K + m := by omega


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.reduceGirard_order_le (pZ : PolyZonotope (Vec ℝ n)) {o : ℕ}
    (ho : 0 < o) : -- --- CONCL ---
    (pZ.reduceGirard o).h + (pZ.reduceGirard o).q ≤ o * n := by -- --- PROOF ---
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold PolyZonotope.reduceGirard
  split_ifs with hlt
  · exact le_trans (PolyZonotope.aux_order_arith (min_le_left _ _)) (le_of_eq hK)
  · exact Nat.le_of_not_lt hlt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
