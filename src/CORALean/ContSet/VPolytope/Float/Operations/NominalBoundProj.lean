import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
import CORALean.ContSet.InflatedContSet.Operations.Bound

/-!
# `VPolytope.nominalBoundProj`

The exact layer's answer is a maximum over the vertex list, so this layer's is
`maximumOver` — no certificate, no rounding, the maximum of stored floats being
one of them.
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

def VPolytope.nominalBoundProj (P : VPolytope 𝕋 n) (j : Fin n) :
    FloatBound 𝕋 (nominalSet P) (LinearMap.proj j) where
  val := maximumOver fun l => P.V j l
  le _ hx :=
    (InflatedContSet.nominal P).le_of_forall_le (LinearMap.proj j)
      (fun l => le_maximumOver (fun l => P.V j l) l) hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
