module

public import CORALean.ContSet.PolyZonotope.Real.Operations.IsExpEdgeAt

@[expose] public section

/-!
# `PolyZonotope.IsExpEdge`

The graph `G_{pZ,η}` of `[1, Def. 5]`, as the relation its edges form: nodes are the dependent
generators and `i → j` holds where `IsExpEdgeAt` does at some index. `[1, Def. 4]` makes that index
the only one at which the two columns differ, so the existential loses nothing. Hiding the
index lets a path be spoken of (`[1, Lemma 1]`); what consumes an edge to relax needs the index
back and takes `IsExpEdgeAt`. The relation is decidable, so the edge set is a `Finset` a
selection can search.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `η` – exponent threshold
* `i` – first generator index
* `j` – second generator index

## Output
* Prop that some factor makes the pair a relaxable edge

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications in
      Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The edges of the generator graph: an edge at whichever index the two
exponent columns differ in. -/
def PolyZonotope.IsExpEdge {p h : ℕ} (E : Fin p → Fin h → ℕ) (η : ℕ) (i j : Fin h) : Prop :=
  ∃ k₀, PolyZonotope.IsExpEdgeAt E η k₀ i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
