module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.ConZonotope.Real.Operations.Plus
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `ConZonotope.intersection`

CORA's `@conZonotope/and_` [1, Prop. 1], and the reason the representation exists: zonotopes
are not closed under intersection and constrained zonotopes are, exactly.

Both coefficient vectors are concatenated and each half keeps its own constraints, exactly as in
`plus`; what intersection adds is one row per coordinate demanding that the two points agree,
`G₁ β₁ - G₂ β₂ = c₂ - c₁`. Only the first generator block is then kept, the second having been
pinned to it. Those rows are the one place a matrix is still assembled, at `Vec` only, since they
read a generator coordinate by coordinate.

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope

## Output
* the intersection of the two sets

## References

* [1] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The rows pinning the two points together, one per coordinate. -/
@[step_of ConZonotope.intersection]
def ConZonotope.step_agreeMat (cZ₁ cZ₂ : ConZonotope (Vec ℝ n)) : Mat ℝ n (cZ₁.h + cZ₂.h) :=
  fun i => Fin.append (fun j => cZ₁.G j i) fun j => -cZ₂.G j i


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.intersection (cZ₁ cZ₂ : ConZonotope (Vec ℝ n)) : ConZonotope (Vec ℝ n) where
  h := cZ₁.h + cZ₂.h
  c := cZ₁.c
  G := Fin.append cZ₁.G 0
  P := ((cZ₁.P.comap (blockLeft cZ₁.h cZ₂.h)).intersection
          (cZ₂.P.comap (blockRight cZ₁.h cZ₂.h))).intersection
        (HPolytope.eqs (ConZonotope.step_agreeMat cZ₁ cZ₂) fun i => cZ₂.c i - cZ₁.c i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
