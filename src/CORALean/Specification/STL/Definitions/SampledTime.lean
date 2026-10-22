module

public import CORALean.Specification.STL.Definitions.Pform

@[expose] public section

/-!
# Sampled time formulas in conjunctive normal form

The input of [1, Lemma 2]: `⋀ᵢ ⋁ⱼ X_c^j (φᵢⱼ ∨ ϱᵢⱼ)` with `φᵢⱼ = ⋁_k F(0,c)ϱ_k ∨ ⋁_l G(0,c)ϱ_l`. A
`Branch` is one `X_c^j(φᵢⱼ ∨ ϱᵢⱼ)` by its `j`, its `ϱᵢⱼ` and the lists `K` of the `ϱ_k` and `L` of
the `ϱ_l`; a `Clause` is a `⋁ⱼ` of branches, and a formula a `⋀ᵢ` of clauses. The step `c` is not
stored.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- One disjunct of a sampled-time clause: a shift `j`, a propositional formula, and the lists of
formulas under finally and under globally. -/
structure STL.Branch (X : Type) where
  j : ℕ
  ϱ : Pform X
  K : List (Pform X)
  L : List (Pform X)

/-- `⋁ⱼ X_c^j(φᵢⱼ ∨ ϱᵢⱼ)`. -/
abbrev STL.Clause (X : Type) : Type := List (STL.Branch X)

/-- `⋀ᵢ ⋁ⱼ X_c^j(φᵢⱼ ∨ ϱᵢⱼ)`. -/
abbrev STL.CNF (X : Type) : Type := List (STL.Clause X)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
