module

public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.Specification.STL.Operations.TreeTemporal

@[expose] public section

/-!
# Moving next inwards

`@stl/combineNext.m`: a `next` is pushed through `&`, `|` (when the operand is temporal) and `~`,
and two nested `next` become one with the sum of their times. Every other node is kept, and so is
a `next` over a non-temporal `&` or `|`. CORA returns a non-temporal formula at once; here the
clauses for `&`, `|` and `~` recurse, which leaves a formula without a `next` as it is.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `combineNext(obj)`. -/
def STL.Tree.combineNext : STL.Tree n → STL.Tree n
  | .next a (.and φ ψ) =>
    if (STL.Tree.and φ ψ).temporal then .and (combineNext (.next a φ)) (combineNext (.next a ψ))
    else .next a (.and φ ψ)
  | .next a (.or φ ψ) =>
    if (STL.Tree.or φ ψ).temporal then .or (combineNext (.next a φ)) (combineNext (.next a ψ))
    else .next a (.or φ ψ)
  | .next a (.not φ) => .not (combineNext (.next a φ))
  | .next a (.next b φ) => combineNext (.next (a + b) φ)
  | .next a φ => .next a φ
  | .and φ ψ => .and (combineNext φ) (combineNext ψ)
  | .or φ ψ => .or (combineNext φ) (combineNext ψ)
  | .not φ => .not (combineNext φ)
  | φ => φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
