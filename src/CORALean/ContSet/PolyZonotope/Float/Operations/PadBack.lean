module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadE

@[expose] public section

/-!
# `PolyZonotope.padBack` over a floating-point scalar

CORA's `restoreId` for the ids missing after a set's own: `r` further factors appended at
exponent zero. The center, both generator blocks and the error box are kept, so nothing
rounds and the set is unchanged.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `r` fresh factors appended after the set's own, at exponent zero. -/
def PolyZonotope.padBack (r : ℕ) (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p + r
  h := pZ.h
  q := pZ.q
  c := pZ.c
  G := pZ.G
  E := Real.PolyZonotope.padE pZ.E r
  GI := pZ.GI
  I_error := pZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
