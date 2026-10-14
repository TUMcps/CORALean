module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.GetSubsetOuter
public import CORALean.ContSet.PolyZonotope.Real.Operations.Resolve

@[expose] public section

/-!
# `PolyZonotope.resolve` over-approximates the exact one

`resolve` is `getSubset` at `[x, x]`, and `0` is exact in the scalar.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.resolve_outer (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) (x : 𝕋) :
    (Real.PolyZonotope.resolve (nominal pZ) k (toReal x)).construct
        + pZ.I_error.construct ⊆ (pZ.resolve k x).construct := by
  have h := PolyZonotope.getSubset_outer pZ k x zero
  rw [toReal_zero] at h
  exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
