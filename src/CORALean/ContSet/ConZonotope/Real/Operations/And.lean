import CORALean.ContSet.ConZonotope.Real.Operations.Plus

/-!
# `ConZonotope.and`

CORA's `@conZonotope/and_`, and the reason the representation exists: zonotopes
are not closed under intersection and constrained zonotopes are, exactly.

Both coefficient vectors are concatenated and each half keeps its own
constraints, exactly as in `plus`; what intersection adds is one row per
coordinate demanding that the two points agree, `G₁ β₁ - G₂ β₂ = c₂ - c₁`. Only
the first generator block is then kept, the second having been pinned to it.

Those rows are the one place a matrix is still assembled, because they are the
one constraint that reads both blocks at once. At `Vec` only, since they read a
generator coordinate by coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- The rows pinning the two points together, one per coordinate. -/
def ConZonotope.agreeMat (C₁ C₂ : ConZonotope (Vec ℝ n)) : Mat ℝ n (C₁.h + C₂.h) :=
  fun i => Fin.append (fun j => C₁.G j i) fun j => -C₂.G j i

def ConZonotope.and (C₁ C₂ : ConZonotope (Vec ℝ n)) : ConZonotope (Vec ℝ n) where
  h := C₁.h + C₂.h
  c := C₁.c
  G := Fin.append C₁.G 0
  P := ((C₁.P.comap (blockLeft C₁.h C₂.h)).and (C₂.P.comap (blockRight C₁.h C₂.h))).and
        (HPolytope.eqs (ConZonotope.agreeMat C₁ C₂) fun i => C₂.c i - C₁.c i)

end CORALean.Real
