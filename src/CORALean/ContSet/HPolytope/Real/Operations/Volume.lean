module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# `HPolytope.volume`

CORA's `@polytope/volume_`: the `n`-dimensional volume of the polytope, which CORA computes by
enumerating the vertices (`'lcon2vert'`) and a convex hull (`convhulln`, or the simplex
determinant for `n + 1` vertices, or `max V - min V` in dimension one). The quantity is the
Lebesgue measure of the set, defined here as `ENNReal` so that infinite measure has a value.
CORA answers `Inf` for every unbounded polytope, a lower-dimensional one included, where the
measure is `0`; and `0` for the empty set and a bounded polytope that is not full-dimensional.
The measure agrees with CORA on every full-dimensional or bounded polytope; the unbounded
lower-dimensional case is not claimed.

## Inputs
* `P` – H-polytope

## Output
* the Lebesgue volume of the polytope
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Lebesgue volume of the polytope. -/
noncomputable def HPolytope.volume (P : HPolytope (Vec ℝ n)) : ENNReal :=
  MeasureTheory.volume P.construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
