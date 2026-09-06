import CORALean.ContSet.PolyZonotope.Real.Operations.Map

/-!
# `PolyZonotope.mtimes`

CORA's `@polyZonotope/mtimes`: `map` at `A *ᵥ ·`, spelt with `*ᵥ` because that is
the form every caller states its matrix in.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

def PolyZonotope.mtimes (M : Mat ℝ m n) (PZ : PolyZonotope (Vec ℝ n)) :
    PolyZonotope (Vec ℝ m) where
  p := PZ.p
  h := PZ.h
  q := PZ.q
  c := M *ᵥ PZ.c
  G := fun i => M *ᵥ PZ.G i
  E := PZ.E
  GI := fun j => M *ᵥ PZ.GI j

end CORALean.Real
