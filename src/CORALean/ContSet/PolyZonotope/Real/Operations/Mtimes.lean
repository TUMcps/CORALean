import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import Mathlib.Data.Matrix.Mul

/-!
# `PolyZonotope.mtimes`

CORA's `@polyZonotope/mtimes`: `map` at `A *ᵥ ·`, spelt with `*ᵥ` because that is
the form every caller states its matrix in.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.mtimes (M : Mat ℝ m n) (pZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) where
  p := pZ.p
  h := pZ.h
  q := pZ.q
  c := M *ᵥ pZ.c
  G := fun i => M *ᵥ pZ.G i
  E := pZ.E
  GI := fun j => M *ᵥ pZ.GI j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
