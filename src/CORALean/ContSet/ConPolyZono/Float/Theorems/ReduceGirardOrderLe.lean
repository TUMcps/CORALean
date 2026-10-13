module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Reduce

@[expose] public section

/-!
# Girard's reduction bounds the generator count

The exact layer's bound, and the same proof: both budgets are clamped, to their
block and to `K = (o-1)·n` between them, so `n·o` follows by arithmetic from the
shape of `reduceBy` alone. Nothing about the scalar enters — the counts are the
`ℕ` fields, which round-off cannot move — and nothing about the ranking does,
which is what leaves `sortPerm`'s unconstrained comparator free.

This is the guarantee the float layer needs most and the exact layer least: over
ℝ an unbounded generator count is a specification that grows, here it is memory
and time per step.

At `o = 0` there is nothing to state: CORA's `K = max(0, N·order - N)` floors
the budget at nothing and the box of `n` is added regardless.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The count arithmetic, and all of it: two budgets summing to at most `K`,
each clamped to the block it cuts, plus the `m` the box adds. -/
theorem ConPolyZono.aux_order_arith {d K h q m : ℕ} (hd : d ≤ K) :
    min d h + (min (K - d) q + m) ≤ K + m := by omega


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.reduceGirard_order_le (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) {o : ℕ} (ho : 0 < o) :
    (cPZ.reduceGirard o).h + (cPZ.reduceGirard o).q ≤ o * n := by -- --- PROOF ---
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold ConPolyZono.reduceGirard
  split_ifs with hlt
  · exact le_trans (ConPolyZono.aux_order_arith (min_le_left _ _)) (le_of_eq hK)
  · exact Nat.le_of_not_lt hlt

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
