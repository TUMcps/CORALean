module

public import CORALean.ContSet.ZonoBundle.Float.Operations.Reduce

@[expose] public section

/-!
# `ZonoBundle.reduce` bounds each member's generator count

The exact layer's bound, member by member: each member of the reduced bundle has at most `o * n`
generators. The proof is `Zonotope.reduceCombastel_order_le`'s, at Girard's rule: below `o * n` the
member is unchanged, above it `reduceBy` writes `(o - 1) * n` kept generators and one box of `n`.

## Inputs
* `zB` – float zonotope bundle
* `o` – maximum order
* `i` – member

## Hypotheses
* `ho` – order positive

## Conclusion
* the `i`-th member of the result has at most `o * n` generators
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.reduce_order_le (zB : ZonoBundle (Vec 𝕋 n)) {o : ℕ} (ho : 0 < o)
    (i : Fin zB.k) : -- --- CONCL ---
    ((zB.reduce o).Z i).h ≤ o * n := by -- --- PROOF ---
  have hK : (o - 1) * n + n = o * n := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n ho)]
  show ((zB.Z i).reduceGirard o).h ≤ o * n
  unfold Zonotope.reduceGirard
  split_ifs with hlt
  · exact le_of_eq hK
  · exact Nat.le_of_not_lt hlt

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
