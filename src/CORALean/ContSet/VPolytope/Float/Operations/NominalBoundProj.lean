module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
public import CORALean.ContSet.InflatedContSet.Operations.Bound

@[expose] public section

/-!
# `VPolytope.nominalBoundProj`

The exact layer's answer is a maximum over the vertex list, so this layer's is
`maximumOver` — no certificate, no rounding, the maximum of stored floats being
one of them.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.nominalBoundProj (P : VPolytope (Vec 𝕋 n)) (j : Fin n) :
    FloatBound 𝕋 (nominalSet P) (LinearMap.proj j) where
  val := maximumOver fun l => P.V l j
  le _ hx :=
    (InflatedContSet.nominal P).le_of_forall_le (LinearMap.proj j)
      (fun l => le_maximumOver (fun l => P.V l j) l) hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
