import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.mtimes`

CORA's `@conZonotope/mtimes`: `map` at `A *ᵥ ·`, spelt with `*ᵥ` because that is
the form every caller states its matrix in.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

def ConZonotope.mtimes (M : Mat ℝ m n) (C : ConZonotope (Vec ℝ n)) : ConZonotope (Vec ℝ m) where
  h := C.h
  c := M *ᵥ C.c
  G := fun j => M *ᵥ C.G j
  P := C.P

end CORALean.Real
