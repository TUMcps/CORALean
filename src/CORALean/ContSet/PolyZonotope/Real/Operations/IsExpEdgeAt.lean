module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff

@[expose] public section

/-!
# `PolyZonotope.IsExpEdgeAt`

The edge condition of `[1, Def. 5]`, read at the one index where the two exponent columns
differ. Nodes are the dependent generators and an edge `i → j` says the pair may be merged:
the columns agree off `k₀` (`[1, Def. 4]`); the exponents there have equal parity or the lower
one is zero; and the lower one is at least the threshold `η`. Its weight is `eDiff`. The parity
condition keeps `eDiff` small and supplies `relaxExpEven_outer`'s hypotheses; soundness needs
none, precision does. Over a bare exponent matrix, so both layers read it; decidable
(`DecidableExpEdgeAt.lean`, `aux_` never marking an instance, issue #62).

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `η` – exponent threshold
* `k₀` – factor index
* `i` – first generator index
* `j` – second generator index

## Output
* Prop that the pair is a relaxable edge at that factor

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

/-- An edge `i → j` at the index `k₀` the two exponent columns differ in:
similar columns, matching parity or a zero below, and no lower than `η`. -/
def PolyZonotope.IsExpEdgeAt {p h : ℕ} (E : Fin p → Fin h → ℕ) (η : ℕ) (k₀ : Fin p)
    (i j : Fin h) : Prop :=
  (∀ k, k ≠ k₀ → E k i = E k j)
    ∧ (E k₀ i % 2 = E k₀ j % 2 ∨ E k₀ j = 0)
    ∧ η ≤ E k₀ j ∧ E k₀ j < E k₀ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
