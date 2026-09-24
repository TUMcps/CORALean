import CORALean.NN.Layers.Layer

/-!
# The reshape layer

CORA's `nnReshapeLayer`: the same numbers read in a different order, the map being
`x ↦ x ∘ e` and `enclose` the same relabelling of the representation. A relabelling is a linear
map, so `Layer.linear` at a permutation matrix would enclose the same set; it is not used, for
the *guarantee*: `Mtimes.mtimes_outer` claims containment and has no room to claim more, and
`Reindex` is that room, one method and one equality. A reshape carries no weights, so there is
no scalar to name and nothing to round, and every representation's `Reindex` is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Reindex

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Reindex S] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `e i` is which input coordinate output coordinate `i` reads. -/
def Layer.reshape (e : Fin m ≃ Fin n) : Layer S n m where
  enclose := reindex e

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
