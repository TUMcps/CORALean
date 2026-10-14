module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.LevelSet.Real.LevelSet

@[expose] public section

/-!
# An ellipsoid as a level set — the construction

`Ellipsoid.levelSet` is the construction; `Ellipsoid_to_LevelSet` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `levelSet(E)`: the single constraint `(x - q)ᵀ (G Gᵀ)⁻¹ (x - q) - 1 ≤ 0`. -/
noncomputable def Ellipsoid.levelSet (E : Ellipsoid n) : LevelSet n where
  m := 1
  f x := fun _ => (x - E.c) ⬝ᵥ ((E.G * E.Gᵀ)⁻¹ *ᵥ (x - E.c)) - 1
  op := fun _ => .le

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
