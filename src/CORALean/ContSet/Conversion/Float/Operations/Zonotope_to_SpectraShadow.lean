module

public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# A zonotope as a spectrahedral shadow, over a floating-point scalar

## Inputs
* `h` – number of generators
* `s` – diagonal entry
* `j` – position of the entry

## Output
* diagonal matrix holding `s` at `j`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The diagonal matrix holding `s` at `j` and zero elsewhere, which is the exact
layer's `diagonal (Pi.single j s)`. -/
def Zonotope.unitDiag {h : ℕ} (s : 𝕋) (j : Fin h) : Mat 𝕋 h h :=
  fun p q => if p = q then (if p = j then s else zero) else zero

/-- The spectrahedral shadow of a zonotope: one pair of diagonal blocks per generator bounds its
coefficient in `[-1, 1]`. -/
def Zonotope.spectraShadow (Z : Zonotope (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) where
  k := Z.h + Z.h
  m := Z.h
  A₀ := blockDiag zero (fun i j => if i = j then one else zero)
    (fun i j => if i = j then one else zero)
  A := fun j => blockDiag zero (Zonotope.unitDiag one j) (Zonotope.unitDiag (neg one) j)
  c := Z.c
  G := Z.G
  I_error := Z.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
