module

public import CORALean.ContSet.Zonotope.Real.Operations.MinnormOffset

@[expose] public section

/-!
# `Zonotope.minnorm`

CORA's `minnorm(Z)` [2]: the smallest offset of the facets of `polytope(Z - c)`, with the rows
`C` normalized to unit length, whose rows with `NaN` (dependent generators) are removed. With unit
rows `b = Δd` is the distance from the centre to each facet's hyperplane, so the minimum is the
distance from the centre to the boundary, which is what the docstring promises ("the point on the
boundary which has minimum distance to the zonotope center"). `Zonotope.minnorm_ball_subset`
and `Zonotope.le_minnorm_of_ball_subset` say that it is the Euclidean radius of the largest
ball around the centre inside `Z`.

The facet rows are the cross products of `n` generators [1, Thm. 2], and the facet description
is exact (`Zonotope.hRep_eq`).

CORA takes `min(b.^2)` and its square root; `b ≥ 0`, so this is the minimum itself.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
* [2] `contSet/@zonotope/minnorm.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `val = sqrt(min(b.^2))` over the facets `S` whose normal is not zero. -/
noncomputable def Zonotope.minnorm (Z : Zonotope (Vec ℝ (n + 1))) : ℝ :=
  sInf (Z.minnormOffset '' {S | Z.facetNormal S ≠ 0})

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
