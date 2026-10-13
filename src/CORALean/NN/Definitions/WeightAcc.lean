module

public import CORALean.NN.Definitions.WeightLayer

@[expose] public section

/-!
# The fused affine map being accumulated

CORA's running `W` and `b` in `getNormalForm`, starting at the scalars `W = 1`, `b = 0`:
`id` is that start, no layer fused yet, and `aff W b` the map `x ↦ W x + b` once one has been.
`id` forces the two dimensions equal, which is what lets an untouched accumulator be dropped.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- Nothing fused yet, or the fused map `x ↦ W x + b`. -/
inductive WeightAcc (α : Type) : ℕ → ℕ → Type where
  | id {n : ℕ} : WeightAcc α n n
  | aff {n d : ℕ} (W : Mat α d n) (b : Fin d → α) : WeightAcc α n d

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
