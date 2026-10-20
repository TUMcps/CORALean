module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Float.Operations.PadVars

@[expose] public section

/-!
# `ConPolyZono.dependent`

Every independent generator made dependent, by giving it a fresh factor that appears in it alone
and to the first power. Nothing is computed, so this operation rounds nothing and is exact.

It is here because `intersection` needs it: the agreement rows constrain the factors, and an
independent coefficient is not one. The fresh factors take exponent zero in every constraint row
(`padE`).

## Inputs
* `cPZ` – constrained polynomial zonotope

## Output
* same set with independent generators made dependent
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.dependent (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cPZ.p + cPZ.qI
  h := cPZ.h + cPZ.qI
  qI := 0
  c := cPZ.c
  G := Fin.append cPZ.G cPZ.GI
  E := Real.PolyZonotope.plusE cPZ.E (Real.PolyZonotope.identE cPZ.qI)
  GI := Fin.elim0
  cons := cPZ.cons.padVars (Interval.unit cPZ.qI)
  cons_eq := cPZ.cons_eq
  cons_dom := Interval.append_eq_unit cPZ.cons_dom rfl
  I_error := cPZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
