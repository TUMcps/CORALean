import CORALean.NN.Layers.Operations.Reshape

/-!
# The reshape layer loses nothing

The only standard layer whose guarantee is an equality, at every scalar: a reindexing moves
stored values without arithmetic, so it rounds nothing even at a machine scalar.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Reindex

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Reindex S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The layer's whole content, and the only `_exact` in `NN` that holds at every scalar. -/
theorem Layer.reshape_exact (e : Fin m ≃ Fin n) (s : S n) :
    construct ((Layer.reshape (S := S) e).enclose s) = reindexLin e '' construct s :=
  reindex_exact e s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
