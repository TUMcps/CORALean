module

public import CORALean.ContSet.Capsule.Float.Operations.Basic

@[expose] public section

/-!
# `Capsule.absorbRounding`

The error box moves into the radius: center and generator held, radius raised by
`Capsule.errorNorm`. The Euclidean norm over points `c + t g + (w + e)` (nominal capsule plus
box) is bounded by `r + ‖e‖₂`; the bound on `‖e‖₂` is the farthest corner's norm, rounded up.
The center stays put (rounding it again costs extra), and the box clears. `k` is the Newton
iterations for sqrt.

## Inputs
* `k` – Newton steps for sqrt
* `C` – capsule with error box

## Output
* the capsule with its error box absorbed into the radius
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
