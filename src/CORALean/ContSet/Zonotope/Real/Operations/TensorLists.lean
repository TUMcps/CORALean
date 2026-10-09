import CORALean.Global.Tensor

/-!
# `Zonotope.TensorLists`

CORA's `options.list` of `tensorMultiplication`: `perm` the permutations (with replacement) of
generator indices, one row per permutation, `comb` the combinations, of which only the row count
is read (here `C`), and `map` sending each permutation to its combination. No CORA code builds
them (they are a leftover of its third-order reachability code), so they are arguments.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- `options.list` for `k` generators: `P` permutations `perm` of generator indices with
replacement, each mapped to one of `C` combinations by `map`. -/
structure Zonotope.TensorLists (k : ℕ) where
  P : ℕ
  C : ℕ
  perm : Fin P → Fin 3 → Fin k
  map : Fin P → Fin C

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
