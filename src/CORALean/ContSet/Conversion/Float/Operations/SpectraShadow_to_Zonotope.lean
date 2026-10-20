module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.SpectraShadow_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemBase
public import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A spectrahedral shadow as a zonotope, over a floating-point scalar

## Inputs
* `S` – spectrahedral shadow
* `Yup` – upper certificate matrices per generator
* `Ylo` – lower certificate matrices per generator

## Output
* zonotope enclosing the shadow, if the certificates hold
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open scoped Matrix

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.zonotope (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k) :
    Option (Zonotope (Vec 𝕋 n)) :=
  (S.base.interval Yup Ylo).map fun B =>
    (Zonotope.mtimes (fun r j => S.G j r) B.zonotope).plus
        ((Interval.point S.c).plus S.I_error).zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
