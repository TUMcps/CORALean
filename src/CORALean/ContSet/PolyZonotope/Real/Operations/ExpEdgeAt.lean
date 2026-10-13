import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff

/-!
# `PolyZonotope.ExpEdgeAt`

The edge condition of `[1, Def. 5]`, read at the one index where the two
exponent columns differ. Nodes are the dependent generators and an edge `i → j`
says the pair may be merged: the columns agree off `k₀`, which is `[1, Def. 4]`;
the exponents there have equal parity or the lower one is zero; and the lower
one is still at least the threshold `η`. Its weight is `eDiff`, already defined.

The parity condition is what keeps `eDiff` small — without it `x^a - x^b`
reaches `2` at `x = -1`. Against an even column it also supplies
`relaxExpEven_outer`'s hypotheses, which is what a selection rule is for here:
soundness needs none, precision does.

Stated over a bare exponent matrix rather than over a set, so both layers read
it — the exponents are naturals in both. `Prop`-valued and decidable, every
clause ℕ arithmetic or a bounded quantifier; the instance is
`DecidableExpEdgeAt.lean`, `aux_` never marking an instance (issue #62).

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
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
def PolyZonotope.ExpEdgeAt {p h : ℕ} (E : Fin p → Fin h → ℕ) (η : ℕ) (k₀ : Fin p)
    (i j : Fin h) : Prop :=
  (∀ k, k ≠ k₀ → E k i = E k j)
    ∧ (E k₀ i % 2 = E k₀ j % 2 ∨ E k₀ j = 0)
    ∧ η ≤ E k₀ j ∧ E k₀ j < E k₀ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
