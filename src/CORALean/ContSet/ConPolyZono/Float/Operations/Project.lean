module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.project` over a floating-point scalar

The center and the rows of both generator blocks at the chosen coordinates; the exponent
matrices and the constraint system constrain the factors, not the coordinates, and are copied.
The error box is projected with `Interval.project`. Selecting coordinates does no arithmetic,
so nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.project (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (dims : Fin m → Fin n) : ConPolyZono
    𝕋 (Vec 𝕋 m) where
  p := cPZ.p
  h := cPZ.h
  qI := cPZ.qI
  c := fun k => cPZ.c (dims k)
  G := fun l k => cPZ.G l (dims k)
  E := cPZ.E
  GI := fun j k => cPZ.GI j (dims k)
  cons := cPZ.cons
  cons_eq := cPZ.cons_eq
  I_error := cPZ.I_error.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
