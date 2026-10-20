module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Relax

@[expose] public section

/-!
# `ConPolyZono.absorbRounding`

Both records of rounding moved into the parameters. The error box becomes independent generators:
one fresh generator per coordinate, as long as the box's larger endpoint (`errorBound`, which
rounds nothing), added to the independent block. Each row's slack becomes a fresh dependent factor
that the row alone reads, with the coefficient `b_error`, as `Real.ConPolyZono.relax` lays it out,
and no generator reads; the slack left is `zero`. Nothing rounds, and the box left over is the
origin. Unlike `dependent`, the independent generators stay independent.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Output
* same set with the rounding error as independent generators
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
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
    p := cPZ.p + cPZ.cons.m
    qI := cPZ.qI + n
    E := Real.ConPolyZono.padE cPZ.E cPZ.cons.m
    GI := Fin.append cPZ.GI (diagonalBlock (PolyZonotope.errorBound cPZ.I_error))
    -- the slack `cons.b_error` of each row, as a factor of its own, the slack left `zero`
    cons := cPZ.cons.relax (Interval.unit cPZ.cons.m)
    cons_eq := cPZ.cons_eq
    cons_dom := Interval.append_eq_unit cPZ.cons_dom rfl
    I_error := Interval.origin n }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
