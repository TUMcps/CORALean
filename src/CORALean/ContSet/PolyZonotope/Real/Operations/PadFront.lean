import CORALean.ContSet.PolyZonotope.Real.Operations.PadFrontE

/-!
# `PolyZonotope.padFront`

`padBack` from the other side: `l` fresh factors *before* the set's own. Again
only the factor count and the exponent matrix move, and again at exponent zero,
so no point and no denoted set changes.

This is the right-hand half of a product over independent factors — the set
whose own factors sit second in the joint numbering.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `l` fresh factors put before the set's own, at exponent zero. -/
def PolyZonotope.padFront (l : ℕ) (pZ : PolyZonotope α) : PolyZonotope α where
  p := l + pZ.p
  h := pZ.h
  q := pZ.q
  c := pZ.c
  G := pZ.G
  E := PolyZonotope.padFrontE l pZ.E
  GI := pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
