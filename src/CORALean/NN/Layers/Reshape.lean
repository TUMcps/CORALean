import CORALean.NN.Layer

/-!
# The reshape layer

CORA's `nnReshapeLayer`: the same numbers read in a different order, `eval` being
`x ↦ x ∘ e` and `enclose` the same relabelling of the representation. The only
standard layer that loses nothing — `reshape_exact` is an equality.

A relabelling is a linear map, so `Layer.linear` at a permutation matrix would
enclose the same set. It is not used here, and the reason is the *guarantee*
rather than the arithmetic: `Mtimes.mtimes_outer` claims containment and has no
room to claim more, so a reshape written that way could not state the one thing
it is for. `Reindex` is that room — one method and one equality. The arithmetic
saving comes along with it, but by `Layers/Convolution`'s argument that alone
would not have justified a class; the exactness does.

A reshape carries no weights, so there is no scalar to name and nothing to round:
this constructor is already the float one, as `Layer.identity` is. What the float
layer owes is the `Reindex` instances, and `ContSet/*/Float` has them — both
equalities, a permutation moving stored floats without arithmetic.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet Reindex

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Reindex S] {n m : ℕ}

/-- Reading a `p × q` array the other way round, which is the reshape a
layout change is. Flattening is not a layer at all — `Vec ℝ (p * q)` is what a
layer sees either way — so this is the only content a reshape has. -/
def Fin.transposeEquiv (p q : ℕ) : Fin (q * p) ≃ Fin (p * q) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin q) (Fin p)).trans finProdFinEquiv)

/-- `e i` is which input coordinate output coordinate `i` reads. -/
def Layer.reshape (e : Fin m ≃ Fin n) : Layer S n m where
  eval x := reindexLin e x
  enclose := reindex e
  enclose_outer s x hx := by
    rw [reindex_exact]
    exact Set.mem_image_of_mem _ hx


-- =======================================  MAIN THEOREM  ======================================= --

/-- The layer's whole content, and the only `_exact` in `NN`. -/
theorem Layer.reshape_exact (e : Fin m ≃ Fin n) (s : S n) :
    construct ((Layer.reshape (S := S) e).enclose s)
      = (Layer.reshape (S := S) e).eval '' construct s :=
  reindex_exact e s

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
