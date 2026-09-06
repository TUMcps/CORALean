import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG

/-!
# The generators of `mul`

Split out of `Mul.lean` (issue #62): read again by the float layer's own
`Theorems/EvalPolyOuter.lean`, `Theorems/MulOuter.lean` and
`Theorems/MulGClose.lean`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- Generator `(i, j)` of the product: the two extended generators, multiplied
coordinate by coordinate. -/
def PolyZonotope.mulG (S₁ S₂ : PolyZonotope (Vec ℝ n)) :
    Fin ((S₁.h + 1) * (S₂.h + 1)) → Vec ℝ n :=
  fun l i => PolyZonotope.extG S₁ (finProdFinEquiv.symm l).1 i
      * PolyZonotope.extG S₂ (finProdFinEquiv.symm l).2 i

end CORALean.Real
