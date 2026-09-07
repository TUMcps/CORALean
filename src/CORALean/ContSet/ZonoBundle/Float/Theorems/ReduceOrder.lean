import CORALean.ContSet.ZonoBundle.Float.Operations.Reduce

/-!
# `ZonoBundle.reduce` bounds the bundle size

The exact layer's bound, and the same proof: `k` is an `ℕ` field `reduce` sets
by `min`, so nothing about the scalar enters.

No `0 < o` hypothesis, unlike `Zonotope.reduceCombastel_order_le`: at `o = 0`
the reduced bundle has `k = 0`, which denotes `univ` — a sound enclosure of
anything, per `ZonoBundle.lean`'s docstring — so the bound holds there too,
where a zonotope with no generators would have had none to keep.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [FloatOps 𝕋] in
theorem ZonoBundle.reduce_order_le (zB : ZonoBundle 𝕋 n) (o : ℕ) : (zB.reduce o).k ≤ o :=
  min_le_right zB.k o

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
