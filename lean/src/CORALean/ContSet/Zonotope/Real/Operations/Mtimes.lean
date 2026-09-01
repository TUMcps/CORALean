import CORALean.ContSet.Zonotope.Real.Operations.Map

/-!
# `Zonotope.mtimes`

CORA's `@zonotope/mtimes`: `map` at `A *ᵥ ·`, spelt with `*ᵥ` because that is
the form every caller states its matrix in.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

def Zonotope.mtimes (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ m) where
  h := Z.h
  c := M *ᵥ Z.c
  G := fun j => M *ᵥ Z.G j

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem Zonotope.mtimes_eq_map (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) :
    Zonotope.mtimes M Z = Z.map (Matrix.mulVecLin M) := rfl

end CORALean.Real
