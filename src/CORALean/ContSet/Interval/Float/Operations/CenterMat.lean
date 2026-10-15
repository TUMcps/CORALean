module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.centerMat`, over a floating-point scalar

Some float matrix inside the box, entrywise: `half` is exact, so only the sum
`inf + sup` rounds, and only downward — the interval-matrix-times-zonotope
enclosure needs no tighter a midpoint than this, only a sound bound on how far
any denoted matrix can be from it, which `Interval.matResidual` states.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Some float matrix inside the box, entrywise: `half` of the downward-rounded
sum of the two bounds. -/
def Interval.centerMat (IM : Interval (Mat 𝕋 m n)) : Mat 𝕋 m n :=
  fun i j => half (addDown (IM.inf i j) (IM.sup i j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
