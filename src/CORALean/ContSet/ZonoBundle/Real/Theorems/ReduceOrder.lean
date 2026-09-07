import CORALean.ContSet.ZonoBundle.Real.Operations.Reduce

/-!
# `ZonoBundle.reduce` bounds the bundle size

Unlike `Zonotope.reduce_order_le`, no `0 < o` hypothesis: at `o = 0` the
reduced bundle has `k = 0`, which denotes `univ` — a sound enclosure of
anything, per `ZonoBundle.lean`'s docstring, so the bound holds there too.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] [Module ℝ α] in
theorem ZonoBundle.reduce_order_le (B : ZonoBundle α) (o : ℕ) : (B.reduce o).k ≤ o :=
  min_le_right B.k o

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
