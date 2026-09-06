import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce

/-!
# `reduceGirard` bounds the generator count

Both budgets are clamped, to their block and to `K = (o-1)·n` between them, so
`n·o` follows by arithmetic from the shape of `reduceBy` alone. Nothing about
the scalar enters — the counts are the `ℕ` fields, which round-off cannot move.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The count arithmetic, and all of it: two budgets summing to at most `K`,
each clamped to the block it cuts, plus the `m` the box adds. -/
theorem PolyZonotope.aux_order_arith {d K h q m : ℕ} (hd : d ≤ K) :
    min d h + (min (K - d) q + m) ≤ K + m := by omega


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.reduceGirard_order_le (PZ : PolyZonotope 𝕋 n) {o : ℕ} (ho : 0 < o) :
    (PZ.reduceGirard o).h + (PZ.reduceGirard o).q ≤ o * n := by
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold PolyZonotope.reduceGirard
  split_ifs with hlt
  · exact le_trans (PolyZonotope.aux_order_arith (min_le_left _ _)) (le_of_eq hK)
  · exact Nat.le_of_not_lt hlt

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
