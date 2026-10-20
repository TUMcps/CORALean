module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceCombastel

@[expose] public section

/-!
# `Zonotope.reduceCombastel` bounds the generator count

`reduceBy`'s shape is the whole argument: `h := q + n`, and at the split `aux_combastelSplit`
builds, `q = (o-1)*n`, so the total is `o*n` outright — no clamping, since a `Zonotope` has one
generator block, unlike `PolyZonotope`, where `PolyZonotope.reduceGirard_order_le` needs one to
bound two blocks together. Girard's rule admits the identical bound by the identical argument,
proved separately at `reduceGirard_order_le`: the two rules differ only in which generators the
ranking keeps, never in what `reduceBy` does with the split. At `o = 0` there is nothing to state,
as for `PolyZonotope`: CORA floors the reduced budget at nothing, so order zero lands at order one.

## Inputs
* `Z` – zonotope
* `o` – target order

## Hypotheses
* `ho` – order positive

## Conclusion
* the result has at most `o n` generators
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceCombastel_order_le (Z : Zonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (Z.reduceCombastel o).h ≤ o * n := by -- --- PROOF ---
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  unfold Zonotope.reduceCombastel
  split_ifs with hlt
  · exact le_of_eq hK
  · exact Nat.le_of_not_lt hlt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
