import CORALean.NN.Layer

/-!
# The reshape layer

CORA's `nnReshapeLayer`: the same numbers read in a different order. `eval` is
the relabelling `x ↦ x ∘ e` and `propagate` is the same relabelling of the
representation, and this is the only standard layer that loses nothing —
`reshape_exact` is an equality where every other layer states an inclusion.

## Which interface, and why not a matrix

A relabelling is a linear map, so `Layer.linear` at a permutation matrix would
propagate the same set through machinery that already exists. It is not used
here, and the reason is the *guarantee* rather than the arithmetic:
`Mtimes.mtimes_outer` claims containment and has no room to claim more, so a
reshape written that way could not state the one thing it is for. `Reindex` is
that room — one method and one equality — and it costs each representation an
instance that is `map` at the relabelling (`Zonotope`) or the two bounds
relabelled (`Interval`).

The arithmetic saving comes along with it: a permutation matrix product spends
`n²` multiplications by zero or one where a relabelling moves `n` numbers. That
saving would not on its own have justified a class — by the argument
`Layers/Convolution` makes, structure in a weight matrix is the float layer's
business — but the exactness does, and the two point the same way.

## No float counterpart

A reshape carries no weights, so there is no scalar to name and nothing to
round: this constructor is already the float one, as `Layer.identity` is. What
the float layer owes is the `Reindex` instances, and `ContSet/*/Float` has them
— both equalities, since a permutation moves stored floats without arithmetic
and the error box travels across untouched.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

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
  propagate := reindex e
  propagate_outer s x hx := by
    rw [reindex_exact]
    exact Set.mem_image_of_mem _ hx

/-- The layer's whole content, and the only `_exact` in `NN`. -/
theorem Layer.reshape_exact (e : Fin m ≃ Fin n) (s : S n) :
    construct ((Layer.reshape (S := S) e).propagate s)
      = (Layer.reshape (S := S) e).eval '' construct s :=
  reindex_exact e s

end CORALean.Real
