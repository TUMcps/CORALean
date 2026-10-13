module

public import CORALean.ContSet.Interval.Float.Operations.CenterBox
public import CORALean.ContSet.Interval.Float.Theorems.CenterGe
public import CORALean.ContSet.Interval.Float.Theorems.CenterLoLe

@[expose] public section

/-!
# `Interval.centerBox` holds the real midpoint

The real midpoint of the stored bounds lies between `centerLo` and `center`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.center_mem_centerBox (I : Interval (Vec 𝕋 n)) :
    I.nominal.center ∈ I.centerBox.construct :=
  fun i => ⟨I.centerLo_le i, I.center_ge i⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
