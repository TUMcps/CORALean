module

public import CORALean.ContSet.ConZonotope.Real.Operations.Intersection

@[expose] public section

/-!
# `ConZonotope.conIntersect`

CORA's `@conZonotope/conIntersect` [1, Prop. 1]: the points of `cZ₁` whose image under `M` lies
in `cZ₂`, `{z ∈ cZ₁ | M z ∈ cZ₂}`. The coefficient vectors of the two sets are stacked and each
keeps its own constraints, as in `intersection`; the one new constraint pins the image to the
second set, `M G₁ β₁ - G₂ β₂ = c₂ - M c₁`, one row per coordinate of the image. The first set's
center and generators are kept, the second block of generators being zero.

`intersection` is the case `M = I`; this takes the second set in the image space.

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope
* `M` – map from the first into the second space

## Output
* the points of the first whose image lies in the second

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The points of `cZ₁` that `M` maps into `cZ₂`. -/
def ConZonotope.conIntersect (cZ₁ : ConZonotope (Vec ℝ n)) (cZ₂ : ConZonotope (Vec ℝ m))
    (M : Mat ℝ m n) : ConZonotope (Vec ℝ n) where
  h := cZ₁.h + cZ₂.h
  c := cZ₁.c
  G := Fin.append cZ₁.G 0
  P := ((cZ₁.P.comap (blockLeft cZ₁.h cZ₂.h)).intersection
          (cZ₂.P.comap (blockRight cZ₁.h cZ₂.h))).intersection
        (HPolytope.eqs
          (fun i => Fin.append (fun j => (M *ᵥ cZ₁.G j) i) fun j => -cZ₂.G j i)
          fun i => cZ₂.c i - (M *ᵥ cZ₁.c) i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
