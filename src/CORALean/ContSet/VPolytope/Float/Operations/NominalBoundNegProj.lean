import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
import CORALean.ContSet.InflatedContSet.Operations.Bound

/-!
# `VPolytope.nominalBoundNegProj`

The opposite coordinate direction, where the negation is taken before the
maximum.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

-- the opposite direction, where the negation is taken before the maximum
def VPolytope.nominalBoundNegProj (P : VPolytope 𝕋 n) (j : Fin n) :
    FloatBound 𝕋 (nominalSet P) (-LinearMap.proj j) where
  val := maximumOver fun l => neg (P.V j l)
  le _ hx :=
    (InflatedContSet.nominal P).le_of_forall_le (-LinearMap.proj j)
      (fun l => by
        show -(toReal (P.V j l)) ≤ toReal (maximumOver fun l => neg (P.V j l))
        rw [← toReal_neg]
        exact le_maximumOver (fun l => neg (P.V j l)) l) hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
