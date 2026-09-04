import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce

/-!
# `PolyZonotope.reduce` bounds the generator count

The other half of what `reduce` is for, and the half no `_outer` theorem sees:
an enclosure the size of the state space is sound too, and so is one whose
representation grows every step. `reduce o` returns at most `n·o` generators,
dependent and independent together, whatever it is called on.

Counting the two blocks together is what makes that true, and it is what
separates `reduce` from `reduceDependent`. The statement below is false of the
latter: each call adds `n` independent generators and removes none, so a
reachability loop grows `q` without limit while every order bound it claims
holds.

The proof is arithmetic. Both budgets are clamped — to their block, and to
`K = (o-1)·n` between them — so the bound never appeals to the ranking, which
keeps a selection rule free to be a heuristic. At `o = 0` there is nothing to
state: CORA floors the budget at nothing and adds the box of `n` regardless, so
order zero lands at order one in both tools.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- The count arithmetic, and all of it: two budgets summing to at most `K`,
each clamped to the block it cuts, plus the `m` the box adds. -/
theorem PolyZonotope.aux_order_arith {d K h q m : ℕ} (hd : d ≤ K) :
    min d h + (min (K - d) q + m) ≤ K + m := by omega

theorem PolyZonotope.reduceGirard_order_le (PZ : PolyZonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (PZ.reduceGirard o).h + (PZ.reduceGirard o).q ≤ o * n := by
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold PolyZonotope.reduceGirard
  split_ifs with hlt
  · exact le_trans (PolyZonotope.aux_order_arith (min_le_left _ _)) (le_of_eq hK)
  · exact Nat.le_of_not_lt hlt

/-- Compacting first only lowers the count it then bounds, so the bound reads
off `reduceGirard` unchanged. -/
theorem PolyZonotope.reduce_order_le (PZ : PolyZonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (PZ.reduce o).h + (PZ.reduce o).q ≤ o * n :=
  PolyZonotope.reduceGirard_order_le PZ.compact ho

end CORALean.Real
