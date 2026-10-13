module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope

@[expose] public section

/-!
# `ConZonotope.mtimes`

CORA's `@conZonotope/mtimes`: `map` at `A *ᵥ ·`, spelt with `*ᵥ` because that is
the form every caller states its matrix in.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.mtimes (M : Mat ℝ m n) (cZ : ConZonotope (Vec ℝ n)) : ConZonotope (Vec ℝ m) where
  h := cZ.h
  c := M *ᵥ cZ.c
  G := fun j => M *ᵥ cZ.G j
  P := cZ.P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
