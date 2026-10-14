module

public import CORALean.ContSet.PolyZonotope.Float.Operations.PadBack
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackExact
public import CORALean.ContSet.PolyZonotope.Real.Instances

@[expose] public section

/-!
# `PolyZonotope.padBack` denotes the same set, in float too

An equality: the stored floats are untouched and the nominal part is the exact layer's
`padBack` of the original's, so the exact theorem carries over with the error box as it was.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.padBack_exact (r : ℕ) (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct = (pZ.padBack r).construct := by -- --- PROOF ---
  show InflatedContSet.nominalSet pZ + pZ.I_error.construct
    = InflatedContSet.nominalSet (pZ.padBack r) + pZ.I_error.construct
  have h : InflatedContSet.nominalSet (pZ.padBack r)
      = ((InflatedContSet.nominal pZ).padBack r).construct := rfl
  rw [h, ← Real.PolyZonotope.padBack_exact]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
