import CORALean.ContSet.Interval.Float.Operations.CenterBox
import CORALean.ContSet.Interval.Float.Theorems.CenterGe
import CORALean.ContSet.Interval.Float.Theorems.CenterLoLe

/-!
# `Interval.centerBox` holds the real midpoint

The real midpoint of the stored bounds lies between `centerLo` and `center`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


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
