module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.VPolytope.Float.Operations.ColumnGap
public import CORALean.ContSet.VPolytope.Float.Operations.PairSum

@[expose] public section

/-!
# `VPolytope.plus`

Every vertex of one added to every vertex of the other, as over ℝ, with each sum
rounded down and the gap to the upper rounding charged to the box. One box
covers the whole vertex list, which is what `columnGap` is for.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Output
* polytope of the pairwise vertex sums
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.plus (P₁ P₂ : VPolytope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) where
  k := P₁.k * P₂.k
  V := VPolytope.pairSum addDown P₁ P₂
  I_error := (P₁.I_error.plus P₂.I_error).plus
        (VPolytope.columnGap (VPolytope.pairSum addDown P₁ P₂)
          (VPolytope.pairSum addUp P₁ P₂))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
