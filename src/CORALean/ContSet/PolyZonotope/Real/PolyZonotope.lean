import CORALean.Global.Entrywise

/-!
# Sparse polynomial zonotopes: the representation

CORA's `polyZonotope`, and [1, Def. 1]: a centre, dependent generators `G` scaled by
monomials in factors `α ∈ [-1,1]ᵖ` read off the exponent matrix `E`, and
independent generators `GI` scaled by their own `β ∈ [-1,1]ᵍ`. The `α` are
*shared*, so the denoted set is generally neither convex nor a zonotope and a
quadratic map stays inside the class. Sparsity is a property of how `E` is
stored, not of what it denotes, so nothing here mentions it.

CORA carries an identifier vector `id` naming each factor. Here identity is
positional — a factor *is* its row index — which is why `plus` lays the two
exponent matrices out block-diagonally rather than overlaying them.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

structure PolyZonotope (α : Type) where
  /-- The dependent factors, shared across all of `G`. -/
  p : ℕ
  /-- The dependent generators. -/
  h : ℕ
  /-- The independent generators. -/
  q : ℕ
  c : α
  G : Fin h → α
  E : Fin p → Fin h → ℕ
  GI : Fin q → α

/-- The monomial `∏ₖ αₖ^{E[k,i]}` scaling dependent generator `i`. Stated over an
exponent matrix rather than over a set, so an operation can name the monomials of
the matrix it is still assembling. -/
def PolyZonotope.monomial {p h : ℕ} (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (i : Fin h) : ℝ := ∏ k, a k ^ E k i

def PolyZonotope.construct (pZ : PolyZonotope α) : Set α :=
  {x | ∃ a : Fin pZ.p → ℝ, ∃ β : Fin pZ.q → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ x = pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i + ∑ j, β j • pZ.GI j}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
