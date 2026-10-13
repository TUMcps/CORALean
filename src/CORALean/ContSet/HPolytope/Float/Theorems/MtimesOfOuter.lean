import CORALean.ContSet.HPolytope.Float.Operations.MtimesOf
import CORALean.ContSet.HPolytope.Float.Operations.SubsetOfBounds

/-!
# The float certified linear image encloses

The same line again, with the direction pulled back through the matrix before
the bound is asked for. The matrix is read at its real value, so the rounding
that produced its entries is not this theorem's business.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n p : ℕ}
variable {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mtimesOf_outer (M : Mat 𝕋 p n) (Aq : Mat 𝕋 q p)
    (u : ∀ i, FloatBound 𝕋 P.construct ((rowLin Aq i).comp (mulVecLin (toRealMat M)))) :
    (toRealMat M *ᵥ ·) '' P.construct ⊆ (HPolytope.mtimesOf M Aq u).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
