module

public import CORALean.NN.Layers.Operations.Reshape

@[expose] public section

/-!
# What the reshape layer encloses

The relabelling itself, `reindexLin e`: `reindex_exact` puts the image of every point inside,
and more — `reshape_exact` is the equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Reindex

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Reindex S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.reshape_sound (e : Fin m ≃ Fin n) :
    (Layer.reshape (S := S) e).Sound (reindexLin e) := by
  refine ⟨fun s x hx => ?_⟩
  show reindexLin e x ∈ construct (reindex e s)
  rw [reindex_exact]
  exact Set.mem_image_of_mem _ hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
