import CORALean.NN.Layers.Theorems.Real.SoftmaxSound

/-!
# The exact softmax layer, as an `Enclose` kind

`Real.Layer.softmax` as a kind: the box `Real.exp` gives, which no scalar evaluates, so the
instance is noncomputable and lives here beside the other specifications. The runnable
softmax is `SoftmaxLayer`. It keeps the dimension, so its only field is `dim`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


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
      exact Layer.softmax_sound.image_subset s

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
