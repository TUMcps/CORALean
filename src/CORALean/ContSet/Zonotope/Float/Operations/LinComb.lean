module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.LinCombGDiff
public import CORALean.ContSet.Zonotope.Float.Operations.Midpoint
public import CORALean.ContSet.Zonotope.Float.Operations.MidpointResidual

@[expose] public section

/-!
# `Zonotope.linComb`

The exact operation's shape, rounded: the centre is `midpoint`, one generator
spans the half-difference of the centres, and the generators are `linCombG`
at the down-rounding. The count stays `h₁ + h₂ + 1` as over ℝ, every rounding
going into the box.

Two charges come out of that. The centre is stored in place of a known
bracket, which is `midpointResidual`; every generator's coefficient ranges
over `[-1,1]`, so its shortfall pulls both ways and is charged by
`generatorError` at `linCombGDiff` — one box for the whole matrix, the centre
generator included.
-/

-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.linComb (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := Z₁.h + Z₂.h + 1
  c := Zonotope.midpoint Z₁.c Z₂.c
  G := fun j i => Zonotope.linCombG addDown subDown Z₁ Z₂ i j
  I_error := (Z₁.I_error.linComb Z₂.I_error).plus
        ((Zonotope.midpointResidual Z₁.c Z₂.c).plus
          (Zonotope.generatorError (Zonotope.linCombGDiff Z₁ Z₂)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
