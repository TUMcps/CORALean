import CORALean.ContSet.PolyZonotope.Float.Operations.Resolve
import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetOuter
import CORALean.ContSet.PolyZonotope.Real.Operations.Resolve

/-!
# `PolyZonotope.resolve` over-approximates the exact one

`resolve` is `getSubset` at `[x, x]`, and `0` is exact in the scalar.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.resolve_outer (pZ : PolyZonotope 𝕋 n) (k : Fin pZ.p) (x : 𝕋) :
    (Real.PolyZonotope.resolve (nominal pZ) k (toReal x)).construct
        + pZ.err.construct ⊆ (pZ.resolve k x).construct := by
  have h := PolyZonotope.getSubset_outer pZ k x zero
  rw [toReal_zero] at h
  exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
