import CORALean.ContSet.ConZonotope.Operations.Map

/-!
# `ConZonotope.mtimes`

CORA's `@conZonotope/mtimes`: `map` at `A *ᵥ ·`, spelt with `*ᵥ` because that is
the form every caller states its matrix in.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

def ConZonotope.mtimes (M : Mat ℝ m n) (C : ConZonotope (Vec ℝ n)) : ConZonotope (Vec ℝ m) where
  h := C.h
  q := C.q
  c := M *ᵥ C.c
  G := fun j => M *ᵥ C.G j
  A := C.A
  b := C.b

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem ConZonotope.mtimes_eq_map (M : Mat ℝ m n) (C : ConZonotope (Vec ℝ n)) :
    ConZonotope.mtimes M C = C.map (Matrix.mulVecLin M) := rfl

end CORALean.Real
