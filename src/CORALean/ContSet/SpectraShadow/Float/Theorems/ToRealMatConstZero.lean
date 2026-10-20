module

public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# The stored zero block reads as the zero matrix

The block `plus` puts opposite a set's own matrices: a constant function of the
stored `zero`, which `SoundFloatArithmetic` says reads as `0`.

## Inputs
* `a` – natural number

## Hypotheses
* none

## Conclusion
* the stored zero block reads as the zero matrix
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.toRealMat_const_zero {a : ℕ} :
    toRealMat (fun (_ _ : Fin a) => (zero : 𝕋)) = 0 := by
  ext i j
  simp [toRealMat, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
