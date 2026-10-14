module

public import CORALean.ContSet.Taylm.Real.Operations.Bounds
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# An array of Taylor models as a box — the construction

`Taylm.interval` is the construction; `Taylm_to_Interval` states and proves what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.interval {m : ℕ} (T : Fin m → Taylm n) : Interval (Vec ℝ m) :=
  ⟨fun i => (T i).bounds.1, fun i => (T i).bounds.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
