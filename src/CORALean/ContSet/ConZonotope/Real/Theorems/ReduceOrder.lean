module

public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce

@[expose] public section

/-!
# `ConZonotope.reduce` bounds the degree-of-freedom order

CORA's order of a constrained zonotope counts the generators the equality rows leave free, and
`reduce` brings it to `o`: at most `o n + mₑ` generators, `mₑ` the result's own equality count.
Above the threshold Girard keeps `(o - 1) n` and boxes into `n + mₑ`; below, the threshold bounds.
`0 < o` is needed, as Girard reserves `n` of the budget for the box (`ZonoBundle`'s needs none).

## Inputs
* `cZ` – constrained zonotope
* `o` – target degree-of-freedom order

## Hypotheses
* `ho` – the order is positive

## Conclusion
* the reduced set has at most `o * n` generators beyond its equality rows
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       01-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduce_order_le (cZ : ConZonotope (Vec ℝ n)) {o : ℕ}
    (ho : 0 < o) : -- --- CONCL ---
    (cZ.reduce o).h ≤ o * n + (cZ.reduce o).P.me := by -- --- PROOF ---
  have hmax : max o 1 = o := max_eq_left ho
  have hbox : (o - 1) * n + n = o * n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel ho]
  unfold ConZonotope.reduce
  dsimp only
  by_cases hlt : max o 1 * n + cZ.compact.P.me < cZ.compact.h
  · rw [dif_pos hlt]
    simp only [ConZonotope.reduceLiftBy, ConZonotope.reduceKeepBy,
      HPolytope.intersection, HPolytope.eqs]
    omega
  · rw [dif_neg hlt]
    rw [hmax] at hlt
    omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
