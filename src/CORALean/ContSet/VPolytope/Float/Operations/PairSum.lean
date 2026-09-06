import CORALean.ContSet.VPolytope.Float.VPolytope

/-!
# `VPolytope.pairSum`

The pairwise vertex sums of two vertex descriptions, rounded whichever way is
asked.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pairwise vertex sums, rounded whichever way is asked. -/
def VPolytope.pairSum (add : 𝕋 → 𝕋 → 𝕋) (P₁ P₂ : VPolytope 𝕋 n) :
    Mat 𝕋 n (P₁.k * P₂.k) :=
  fun i l => add (P₁.V i (finProdFinEquiv.symm l).1) (P₂.V i (finProdFinEquiv.symm l).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
