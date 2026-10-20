module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Definitions.SampledTime

@[expose] public section

/-!
# A normal form as a sampled time formula

The STL formula `⋀ᵢ ⋁ⱼ X_c^j (φᵢⱼ ∨ ϱᵢⱼ)` of [1, Sec. 4.1] a `CNF` stands for, `X_c^j` as
`X_{jc}`: what `Υ` of [1, Lemma 2] is proved sound and complete for.

Real-only, a specification: it rewrites or builds formulas, whose time bounds and constants are
part of the syntax and are copied or added exactly, never rounded.

## Inputs
* `c` – time step
* `cnf` – normal form

## Output
* the sampled time formula of the normal form

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

open scoped NNReal

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⋀ᵢ ⋁ⱼ X_c^j (φᵢⱼ ∨ ϱᵢⱼ)`. -/
def STL.CNF.toFormula (c : ℝ≥0) (cnf : STL.CNF X) : STL.Formula X :=
  -- `⋁_k F(0,c) ϱ_k` and `⋁_l G(0,c) ϱ_l`
  let finals := fun K : List (Pform X) =>
    STL.Formula.bigOr (K.map fun ϱ => .finOpen c (.ofPform ϱ))
  let globals := fun L : List (Pform X) =>
    STL.Formula.bigOr (L.map fun ϱ => .globOpen c (.ofPform ϱ))
  -- `X_c^j (φᵢⱼ ∨ ϱᵢⱼ)` with `φᵢⱼ = ⋁_k F(0,c) ϱ_k ∨ ⋁_l G(0,c) ϱ_l`
  let branch := fun b : STL.Branch X =>
    STL.Formula.next (b.j * c) (.or (.or (finals b.K) (globals b.L)) (.ofPform b.ϱ))
  -- `⋁ⱼ` inside a clause, `⋀ᵢ` across clauses
  STL.Formula.bigAnd (cnf.map fun clause => STL.Formula.bigOr (clause.map branch))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
