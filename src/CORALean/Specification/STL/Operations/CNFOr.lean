module

public import CORALean.Specification.STL.Operations.ClauseMerge

@[expose] public section

/-!
# The disjunction of two normal forms

`X_c(ϕ₁ ∨ ϕ₂)`-free distribution of [1, Sec. 4.1]: `(⋀ᵢ cᵢ) ∨ (⋀ⱼ dⱼ)` is `⋀ᵢⱼ (cᵢ ∨ dⱼ)`, each
`cᵢ ∨ dⱼ` one clause.

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

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The clauses `cl₁ ∨ cl₂` for `cl₁` in `a` and `cl₂` in `b`. -/
def STL.CNF.or (a b : STL.CNF X) : STL.CNF X :=
  a.flatMap fun cl₁ => b.map fun cl₂ => STL.Clause.merge cl₁ cl₂


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
