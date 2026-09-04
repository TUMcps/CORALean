import CORALean.ContSet.Zonotope.Real.Operations.Reduce

/-!
# `Zonotope.reduceCombastel` bounds the generator count

`reduceBy`'s shape is the whole argument: `h := q + n`, and at the split
`aux_combastelSplit` builds, `q = (o-1)*n`, so the total is `o*n` outright —
no clamping, since a `Zonotope` has one generator block, unlike `PolyZonotope`,
where `reduceGirard_order_le` needs one to bound two blocks together.

Girard's rule admits the identical bound by the identical argument; it is not
stated here, since this addition is scoped to Combastel's rule alone.

At `o = 0` there is nothing to state, as for `PolyZonotope`: CORA floors the
reduced budget at nothing, so order zero lands at order one in both tools.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem Zonotope.reduceCombastel_order_le (Z : Zonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (Z.reduceCombastel o).h ≤ o * n := by
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold Zonotope.reduceCombastel
  split_ifs with hlt
  · exact le_of_eq hK
  · exact Nat.le_of_not_lt hlt

end CORALean.Real
