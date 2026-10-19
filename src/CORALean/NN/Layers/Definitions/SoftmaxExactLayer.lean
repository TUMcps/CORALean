module

public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Layers.Theorems.Real.SoftmaxEncloses

@[expose] public section

/-!
# The exact softmax layer, as an `Enclose` kind

`Real.Layer.softmax` as a kind: the box `Real.exp` gives, which no scalar evaluates, so the
instance is noncomputable and lives here beside the other specifications. The runnable
softmax is `SoftmaxLayer`. It keeps the dimension, so its only field is `dim`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [IntervalOuter S] [OfInterval S]


-- ========================================  MAIN TYPE  ========================================= --

structure SoftmaxLayer (n m : ℕ) : Type where
  dim : n = m

noncomputable instance : Enclose SoftmaxLayer S where
  eval := fun {n m} l => match n, m, l with
    | _, _, ⟨rfl⟩ => Erased.mk softmax
  enclose := fun {n m} l => match n, m, l with
    | _, _, ⟨rfl⟩ => (Layer.softmax (S := S)).enclose
  enclose_outer := fun {n m} l s => match n, m, l with
    | _, _, ⟨rfl⟩ => by
      rw [Erased.out_mk]
      exact Layer.softmax_encloses.image_subset s

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
