module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.SpectraShadow.Float.Operations.Materialise
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.materialise_eq`

`materialise` is the identity: it changes only what running the definition costs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [FloatOps 𝕋] in
@[simp] theorem SpectraShadow.materialise_eq (S : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    S.materialise = S := by
  simp [SpectraShadow.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
