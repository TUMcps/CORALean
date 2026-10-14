module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# An array of float Taylor models as a float box — the construction

`Taylm.interval` is the construction; `Taylm_to_Interval` states and proves what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.interval {m : ℕ} (T : Fin m → Taylm 𝕋 n) : Interval (Vec 𝕋 m) :=
  ⟨fun i => (T i).bounds.1, fun i => (T i).bounds.2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
