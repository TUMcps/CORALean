module

public import CORALean.Global.Float.Interfaces
public import CORALean.Specification.STL.Definitions.Tree
public import CORALean.Specification.STL.Operations.TreeTemporal

@[expose] public section

/-!
# Moving next inwards, at float

`combineNext` over time bounds of a float scalar. Two nested `next` are merged only when both
bounds are nonnegative and the rounded-up and rounded-down sums agree, so the stored sum is the
exact one; otherwise they stay nested, which means the same.

## Inputs
* none

## Output
* the formula with next moved inwards
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps

variable {𝕋 κ : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `combineNext(obj)` with the sum of two nested `next` times kept only where it is exact. -/
def STL.Tree.combineNextFloat : STL.Tree 𝕋 κ n → STL.Tree 𝕋 κ n
  | .next a (.and φ ψ) =>
    if (STL.Tree.and φ ψ).temporal then
      .and (combineNextFloat (.next a φ)) (combineNextFloat (.next a ψ))
    else .next a (.and φ ψ)
  | .next a (.or φ ψ) =>
    if (STL.Tree.or φ ψ).temporal then
      .or (combineNextFloat (.next a φ)) (combineNextFloat (.next a ψ))
    else .next a (.or φ ψ)
  | .next a (.not φ) => .not (combineNextFloat (.next a φ))
  | .next a (.next b φ) =>
    if le zero a && le zero b && le (addUp a b) (addDown a b) then
      combineNextFloat (.next (addUp a b) φ)
    else .next a (combineNextFloat (.next b φ))
  | .next a φ => .next a φ
  | .and φ ψ => .and (combineNextFloat φ) (combineNextFloat ψ)
  | .or φ ψ => .or (combineNextFloat φ) (combineNextFloat ψ)
  | .not φ => .not (combineNextFloat φ)
  | φ => φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
