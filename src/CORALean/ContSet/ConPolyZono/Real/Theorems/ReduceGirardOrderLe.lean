module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceGirard

@[expose] public section

/-!
# Girard's reduction bounds the generator count

`reduceGirard o` returns at most `o·n` generators, dependent and independent together. The proof
is arithmetic: both budgets are clamped, to their block and to `K = (o-1)·n` between them, so the
bound never appeals to the ranking. At `o = 0` there is nothing to state: CORA floors the budget
at nothing and adds the box of `n` regardless. The constraint counts `m` and `q` are outside this:
only `compact` moves them.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `o` – target order

## Hypotheses
* `ho` – target order is positive

## Conclusion
* the generator count is at most the order times the dimension
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The count arithmetic, and all of it: two budgets summing to at most `K`,
each clamped to the block it cuts, plus the `m` the box adds. -/
theorem ConPolyZono.aux_order_arith {d K h qI m : ℕ} (hd : d ≤ K) :
    min d h + (min (K - d) qI + m) ≤ K + m := by omega


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.reduceGirard_order_le (cPZ : ConPolyZono (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (cPZ.reduceGirard o).h + (cPZ.reduceGirard o).qI ≤ o * n := by -- --- PROOF ---
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold ConPolyZono.reduceGirard
  split_ifs with hlt
  · exact le_trans (ConPolyZono.aux_order_arith (min_le_left _ _)) (le_of_eq hK)
  · exact Nat.le_of_not_lt hlt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
