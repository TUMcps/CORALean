module

public import CORALean.ContSet.Capsule.Float.Operations.Basic

@[expose] public section

/-!
# `Capsule.absorbRounding`

The error box moved into the radius: center and generator kept, the radius raised by
`Capsule.errorNorm`, a bound on the Euclidean norm of every point of the box, and the box of the
result the origin. The norm is the Euclidean one because the capsule's ball is: a point
`c + t g + w` of the nominal capsule (`‖w‖₂ ≤ r`) plus a point `e` of the box is
`c + t g + (w + e)` with `‖w + e‖₂ ≤ r + ‖e‖₂` by the triangle inequality, so a radius at least
`r + ‖e‖₂` for every `e` holds it. The bound is the norm of the larger end magnitude per
coordinate, the largest `‖e‖₂` over the box (its farthest corner), rounded up. Moving the center
to the box's midpoint would cost only the half-widths, but rounds the center again; the center
stays, and with the raised radius rounded up nothing is left in the box.
`k` is the number of Newton steps of the root (`Global/Float/Sqrt`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The capsule with the error box in its radius: `r + errorNorm`, rounded up, and no box. -/
def Capsule.absorbRounding (k : ℕ) (C : Capsule 𝕋 n) : Capsule 𝕋 n where
  c := C.c
  g := C.g
  r := addUp C.r (C.errorNorm k)
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
