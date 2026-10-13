module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard

@[expose] public section

/-!
# `Zonotope.reduceGirard` bounds the generator count

`reduceBy`'s shape is the whole argument: `h := q + n`, and at the split
`girardSplit` builds, `q = (o-1)*n`, so the total is `o*n` outright — no
clamping, since a `Zonotope` has one generator block, unlike `PolyZonotope`,
where `PolyZonotope.reduceGirard_order_le` needs one to bound two blocks
together. Word for word `reduceCombastel_order_le`'s proof: the metric never
appears in either.

At `o = 0` there is nothing to state, as for `PolyZonotope`: CORA floors the
reduced budget at nothing, so order zero lands at order one in both tools.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceGirard_order_le (Z : Zonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (Z.reduceGirard o).h ≤ o * n := by -- --- PROOF ---
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold Zonotope.reduceGirard
  split_ifs with hlt
  · exact le_of_eq hK
  · exact Nat.le_of_not_lt hlt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
