import CORALean.ContSet.ConZonotope.Real.Operations.AgreeMat
import CORALean.ContSet.ConZonotope.Real.Operations.Plus
import CORALean.ContSet.HPolytope.Real.Operations.Eqs

/-!
# `ConZonotope.intersection`

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
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.intersection (cZ₁ cZ₂ : ConZonotope (Vec ℝ n)) : ConZonotope (Vec ℝ n) where
  h := cZ₁.h + cZ₂.h
  c := cZ₁.c
  G := Fin.append cZ₁.G 0
  P := ((cZ₁.P.comap (blockLeft cZ₁.h cZ₂.h)).intersection
          (cZ₂.P.comap (blockRight cZ₁.h cZ₂.h))).intersection
        (HPolytope.eqs (ConZonotope.agreeMat cZ₁ cZ₂) fun i => cZ₂.c i - cZ₁.c i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
