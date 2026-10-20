module

public import CORALean.ContSet.ConZonotope.Real.Operations.ReduceKeep

@[expose] public section

/-!
# `ConZonotope.reduceKeep` bounds the generator count

Above the order the result has `(o - 1) * n + n` generators, which is `o * n` once
`0 < o`: the same budget as Girard's rule, `n` of it for the box. At or below the
order `cZ` passes through and the branch condition is the bound.

## Inputs
* `cZ` – constrained zonotope
* `o` – target order

## Hypotheses
* `ho` – the order is positive

## Conclusion
* the reduced set has at most o * n generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduceKeep_order_le (cZ : ConZonotope (Vec ℝ n)) {o : ℕ}
    (ho : 0 < o) : -- --- CONCL ---
    (cZ.reduceKeep o).h ≤ o * n := by -- --- PROOF ---
  unfold ConZonotope.reduceKeep
  split_ifs with hlt
  · -- `(o - 1) * n + n = o * n`
    show (o - 1) * n + n ≤ o * n
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ho.ne'
    simp [Nat.succ_mul]
  · exact Nat.le_of_not_lt hlt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
