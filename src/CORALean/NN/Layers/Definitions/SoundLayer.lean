import CORALean.NN.Layers.Layer

/-!
# A layer, its kind forgotten

What `Enclose` asks of a kind, for one layer: its function, its propagation and the guarantee
tying them. It lives in `Type` whatever universe the kind it came from lives in, which is
what lets a network, a `Type 1` kind, go into another as a layer, and a layer whose guarantee
comes from somewhere other than a kind — a refinable layer at a pattern — go into one at all.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

structure SoundLayer (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n m : ℕ) where
  eval : Erased (Vec ℝ n → Vec ℝ m)
  enclose : S n → S m
  enclose_outer (s : S n) : eval.out '' construct s ⊆ construct (enclose s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
