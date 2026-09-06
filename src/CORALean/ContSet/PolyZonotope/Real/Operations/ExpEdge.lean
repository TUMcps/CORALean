import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdgeAt

/-!
# `PolyZonotope.ExpEdge`

The graph `G_{PZ,η}` of `[1, Def. 5]`, as the relation its edges form: nodes are
the dependent generators and `i → j` holds where `ExpEdgeAt` does at some index.
`[1, Def. 4]` makes that index the only one at which the two columns differ, so
the existential loses nothing.

Hiding the index is what lets a path be spoken of at all — the graph is a
relation on nodes, and `[1, Lemma 1]` is a statement about paths in it. What
consumes an edge in order to relax needs the index back, and takes `ExpEdgeAt`.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- The edges of the generator graph: an edge at whichever index the two
exponent columns differ in. -/
def PolyZonotope.ExpEdge {p h : ℕ} (E : Fin p → Fin h → ℕ) (η : ℕ) (i j : Fin h) : Prop :=
  ∃ k₀, PolyZonotope.ExpEdgeAt E η k₀ i j

end CORALean.Real
