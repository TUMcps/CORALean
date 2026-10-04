import CORALean.ContSet.PolyZonotope.Float.Operations.OuterApprox
import CORALean.ContSet.PolyZonotope.Float.Theorems.BoxOutOuter

/-!
# `outerApprox` encloses the original, in float too

Whatever `tol` and `id` are: the selection is a heuristic and `boxOut_outer` holds for every
selection. Not exact; the taken independent generators stay in `GI` as in CORA, so their radius
is counted twice.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.outerApprox_outer (pZ : PolyZonotope 𝕋 n) (tol : 𝕋)
    (S : Finset (Fin pZ.p)) : pZ.construct ⊆ (pZ.outerApprox tol S).construct :=
  PolyZonotope.boxOut_outer pZ _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
