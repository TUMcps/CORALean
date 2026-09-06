import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceGirard

/-!
# Girard's reduction bounds the generator count

`reduceGirard o` returns at most `o·n` generators, dependent and independent
together. Counting the two blocks together is what makes that true.

The proof is arithmetic. Both budgets are clamped — to their block, and to
`K = (o-1)·n` between them — so the bound never appeals to the ranking, which
keeps a selection rule free to be a heuristic. At `o = 0` there is nothing to
state: CORA floors the budget at nothing and adds the box of `n` regardless.

The constraint counts `m` and `s` are outside this: the ranking copies them, so
`compact` is the only stage that moves them and the only bound they have.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The count arithmetic, and all of it: two budgets summing to at most `K`,
each clamped to the block it cuts, plus the `m` the box adds. -/
theorem ConPolyZono.aux_order_arith {d K h q m : ℕ} (hd : d ≤ K) :
    min d h + (min (K - d) q + m) ≤ K + m := by omega


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.reduceGirard_order_le (C : ConPolyZono (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (C.reduceGirard o).h + (C.reduceGirard o).q ≤ o * n := by -- --- PROOF ---
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold ConPolyZono.reduceGirard
  split_ifs with hlt
  · exact le_trans (ConPolyZono.aux_order_arith (min_le_left _ _)) (le_of_eq hK)
  · exact Nat.le_of_not_lt hlt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
