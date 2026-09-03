import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce

/-!
# `PolyZonotope.reduce` bounds the generator count

The exact layer's bound, and the same proof: both budgets are clamped, to their
block and to `K = (o-1)·n` between them, so `n·o` follows by arithmetic from the
shape of `reduceBy` alone. Nothing about the scalar enters — the counts are the
`ℕ` fields, which round-off cannot move — and nothing about the ranking does,
which is what leaves `sortPerm`'s unconstrained comparator free.

This is the guarantee the float layer needs most and the exact layer least: over
ℝ an unbounded generator count is a specification that grows, here it is memory
and time per step. It is false of `reduceDependent`, which is what that rule
trades for a tighter step.

At `o = 0` there is nothing to state: CORA's `K = max(0, N·order - N)` floors
the budget at nothing and the box of `n` is added regardless, so order zero
lands at order one in both tools.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The count arithmetic, and all of it: two budgets summing to at most `K`,
each clamped to the block it cuts, plus the `m` the box adds. -/
theorem PolyZonotope.aux_order_arith {d K h q m : ℕ} (hd : d ≤ K) :
    min d h + (min (K - d) q + m) ≤ K + m := by omega

theorem PolyZonotope.reduceGirard_order_le (PZ : PolyZonotope 𝕋 n) {o : ℕ} (ho : 0 < o) :
    (PZ.reduceGirard o).h + (PZ.reduceGirard o).q ≤ o * n := by
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold PolyZonotope.reduceGirard
  split_ifs with hlt
  · exact le_trans (PolyZonotope.aux_order_arith (min_le_left _ _)) (le_of_eq hK)
  · exact Nat.le_of_not_lt hlt

/-- Compacting first only lowers the count it then bounds, so the bound reads
off `reduceGirard` unchanged. -/
theorem PolyZonotope.reduce_order_le (PZ : PolyZonotope 𝕋 n) {o : ℕ} (ho : 0 < o) :
    (PZ.reduce o).h + (PZ.reduce o).q ≤ o * n :=
  PolyZonotope.reduceGirard_order_le PZ.compact ho

end CORALean.Float
