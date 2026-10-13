module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceGirardOrderLe

@[expose] public section

/-!
# `ConPolyZono.reduce` bounds the generator count

Compacting first only lowers the count `reduceGirard_order_le` then bounds, so
the bound reads off unchanged. It bounds the two generator blocks and nothing
else: the ranking copies `m` and `s`, so the constraint counts are `compact`'s
to lower and no order argument reaches them.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.reduce_order_le (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) {o : ℕ} (ho : 0 < o) :
    (cPZ.reduce o).h + (cPZ.reduce o).q ≤ o * n :=
  ConPolyZono.reduceGirard_order_le cPZ.compact ho

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
