import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.VPolytope.Float.Operations.ColumnGap

/-!
# `VPolytope.plus`

Every vertex of one added to every vertex of the other, as over ℝ, with each sum
rounded down and the gap to the upper rounding charged to the box. One box
covers the whole vertex list, which is what `columnGap` is for.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The pairwise vertex sums, rounded whichever way is asked. -/
def VPolytope.pairSum (add : 𝕋 → 𝕋 → 𝕋) (P₁ P₂ : VPolytope 𝕋 n) :
    Mat 𝕋 n (P₁.k * P₂.k) :=
  fun i l => add (P₁.V i (finProdFinEquiv.symm l).1) (P₂.V i (finProdFinEquiv.symm l).2)

def VPolytope.plus (P₁ P₂ : VPolytope 𝕋 n) : VPolytope 𝕋 n where
  k := P₁.k * P₂.k
  V := VPolytope.pairSum addDown P₁ P₂
  E := (P₁.E.plus P₂.E).plus
        (VPolytope.columnGap (VPolytope.pairSum addDown P₁ P₂)
          (VPolytope.pairSum addUp P₁ P₂))

end CORALean.Float
