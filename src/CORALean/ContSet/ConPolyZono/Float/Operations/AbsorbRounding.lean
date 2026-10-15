module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound

@[expose] public section

/-!
# `ConPolyZono.absorbRounding`

The error box made into independent generators: one fresh generator per coordinate, as long as the
box's larger endpoint (`errorBound`, which rounds nothing), added to the independent block. An
independent coefficient meets no constraint and no monomial, so the dependent part, the constraints
and their exponents are left as they are. Nothing rounds, and the box left over is the origin.
Unlike `dependent`, the independent generators stay independent.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The error box as `n` further independent generators, the box left over the origin. -/
def ConPolyZono.absorbRounding (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  { cPZ with
    qI := cPZ.qI + n
    GI := Fin.append cPZ.GI (diagonalBlock (PolyZonotope.errorBound cPZ.I_error))
    I_error := Interval.origin n }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
