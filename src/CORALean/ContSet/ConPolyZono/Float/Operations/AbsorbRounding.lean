module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound

@[expose] public section

/-!
# `ConPolyZono.absorbRounding`

Both records of rounding moved into the parameters. The error box becomes independent generators:
one fresh generator per coordinate, as long as the box's larger endpoint (`errorBound`, which
rounds nothing), added to the independent block. Each row's slack becomes a fresh dependent factor
that the row alone reads, with the coefficient `b_error`, as `Real.ConPolyZono.relax` lays it out,
and no generator reads; the slack left is `zero`. Nothing rounds, and the box left over is the
origin. Unlike `dependent`, the independent generators stay independent.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The error box as `n` further independent generators, the slack of each row as a factor of
its own, the box left over the origin and the slack `zero`. -/
def ConPolyZono.absorbRounding (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  { cPZ with
    p := cPZ.p + cPZ.m
    qI := cPZ.qI + n
    q := cPZ.q + cPZ.m
    E := Real.ConPolyZono.padE cPZ.E cPZ.m
    GI := Fin.append cPZ.GI (diagonalBlock (PolyZonotope.errorBound cPZ.I_error))
    A := fun i => Fin.append (cPZ.A i) (diagonalBlock cPZ.b_error i)
    b_error := fun _ => zero
    R := Real.PolyZonotope.plusE cPZ.R (Real.PolyZonotope.identE cPZ.m)
    I_error := Interval.origin n }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
