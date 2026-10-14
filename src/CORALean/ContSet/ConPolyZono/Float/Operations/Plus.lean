module

public import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.Plus

@[expose] public section

/-!
# `ConPolyZono.plus`

`PolyZonotope.plus` with the two constraint systems carried along side by side,
and the reason it refines is that the carrying is pure bookkeeping: `plusA`
places the two matrices block-diagonally with `zero` in the off-blocks and `b`
concatenates, so not one entry of the constraint system is computed. Only the
centre rounds, exactly as for an unconstrained polynomial zonotope.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.plus (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cPZ₁.p + cPZ₂.p
  h := cPZ₁.h + cPZ₂.h
  q := cPZ₁.q + cPZ₂.q
  m := cPZ₁.m + cPZ₂.m
  s := cPZ₁.s + cPZ₂.s
  c := fun i => addDown (cPZ₁.c i) (cPZ₂.c i)
  G := Fin.append cPZ₁.G cPZ₂.G
  E := Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E
  GI := Fin.append cPZ₁.GI cPZ₂.GI
  A := ConPolyZono.plusA cPZ₁.A cPZ₂.A
  b := ConPolyZono.plusB cPZ₁.b cPZ₂.b
  EC := Real.PolyZonotope.plusE cPZ₁.EC cPZ₂.EC
  err := (cPZ₁.err.plus cPZ₂.err).plus (PolyZonotope.centerResidual cPZ₁.c cPZ₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
