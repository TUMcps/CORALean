module

public import CORALean.Global.Tensor
public import CORALean.NN.Layers.Layer

@[expose] public section

/-!
# `NN/Layers/Definitions`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  `IdentityLayer`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The identity as an `Enclose` kind, which a skip connection is written with. It has no weights
but `dim`, the proof that the two dimensions agree, which `rfl` discharges where a layer is
built; `: Type` keeps a structure of one proof out of `Prop`. -/
structure IdentityLayer (n m : ℕ) : Type where
  dim : n = m


-- ======================================  `Layer.Sound`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

/-- The obligation `Layer` no longer carries: what `enclose` encloses. -/
structure Layer.Sound (L : Layer S n m) (f : Vec ℝ n → Vec ℝ m) : Prop where
  enclose_outer (s : S n) (x : Vec ℝ n) (hx : x ∈ construct s) :
    f x ∈ construct (L.enclose s)


-- ======================================  `LinearLayer`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `nnLinearLayer` as an `Enclose` kind: `W` and `b`, stored in the scalar. The layer
encloses the affine map they denote, read as reals: reading a network off a file is exact. -/
structure LinearLayer (𝕋 : Type) (n m : ℕ) where
  W : Mat 𝕋 m n
  b : Vec 𝕋 m


-- ======================================  `ReshapeLayer`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `nnReshapeLayer` as an `Enclose` kind: the relabelling `e`, output `i` reading input
`e i`. It stores no scalar, so it is one kind at every scalar. -/
structure ReshapeLayer (n m : ℕ) where
  e : Fin m ≃ Fin n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
