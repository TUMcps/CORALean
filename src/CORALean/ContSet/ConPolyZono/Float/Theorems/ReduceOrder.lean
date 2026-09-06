import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceGirardOrderLe

/-!
# `ConPolyZono.reduce` bounds the generator count

Compacting first only lowers the count `reduceGirard_order_le` then bounds, so
the bound reads off unchanged. It bounds the two generator blocks and nothing
else: the ranking copies `m` and `s`, so the constraint counts are `compact`'s
to lower and no order argument reaches them.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.reduce_order_le (C : ConPolyZono 𝕋 n) {o : ℕ} (ho : 0 < o) :
    (C.reduce o).h + (C.reduce o).q ≤ o * n :=
  ConPolyZono.reduceGirard_order_le C.compact ho

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
