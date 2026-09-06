import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadEval

/-!
# The generators of `quadMap`

Split out of `QuadMap.lean` (issue #62): read again by the float layer's own
`Theorems/QuadMapOuter.lean` and by `ConPolyZono.quadMapDep`, both outside
this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Generator `(i, j)` of the image: `Gᵢᵀ Q Gⱼ`, one coordinate per matrix. -/
def PolyZonotope.quadMapG {n m : ℕ} (Q : Fin m → Mat ℝ n n) (S : PolyZonotope (Vec ℝ n)) :
    Fin ((S.h + 1) * (S.h + 1)) → Vec ℝ m :=
  fun l k => PolyZonotope.extG S (finProdFinEquiv.symm l).1
      ⬝ᵥ (Q k *ᵥ PolyZonotope.extG S (finProdFinEquiv.symm l).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
