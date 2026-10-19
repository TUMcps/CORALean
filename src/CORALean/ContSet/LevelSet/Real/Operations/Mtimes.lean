module

public import CORALean.ContSet.LevelSet.Real.LevelSet
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `LevelSet.mtimes`

The image of a level set under an invertible matrix. CORA's `levelSet` has no such method; it is
a preimage substitution in `f`, so a level set answers it exactly where most representations only
enclose.

## Inputs
* `M` – invertible matrix
* `L` – level set

## Output
* level set whose points `y` have `M⁻¹ y` in `L`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `M L` for invertible `M`: `y` is in it when `M⁻¹ y` is in `L`. -/
noncomputable def LevelSet.mtimes (M : Mat ℝ n n) (L : LevelSet n) : LevelSet n where
  m := L.m
  f y := L.f (M⁻¹ *ᵥ y)
  op := L.op

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
