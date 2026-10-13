module

public import CORALean.Global.Tensor

@[expose] public section

/-!
# The layers a network can be normalised over

The weights of the layer types CORA's `getNormalForm` reads: `nnLinearLayer` (`W`, `b`),
`nnElementwiseAffineLayer` (`scale`, `offset`), `nnIdentityLayer` and any pointwise activation,
opaque as the function `f` it applies. Over a semiring `α`, which is all the fusion needs, so
that it runs at an exact scalar. Convolutions are brought to `linear` before, as CORA does, and
reshapes are not covered.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- One layer of `n` inputs and `m` outputs, weights in `α`. -/
inductive WeightLayer (α : Type) : ℕ → ℕ → Type where
  | linear {n m : ℕ} (W : Mat α m n) (b : Fin m → α) : WeightLayer α n m
  | elementwiseAffine {n : ℕ} (scale offset : Fin n → α) : WeightLayer α n n
  | identity {n : ℕ} : WeightLayer α n n
  | activation {n : ℕ} (f : α → α) : WeightLayer α n n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
