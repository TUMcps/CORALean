module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# `HPolytope.facetNormal`

`[1, Sec. 2.3]`: "for a polytope `s = aᵢ`, `i` being an index where maximum or minimum in (1) is
achieved", with `‖s‖ = 1` demanded by the reflection step. The paper's `aᵢ` is the row of the
inequality `(aᵢ, x) ≤ bᵢ`; it is a unit vector only if the row is normalized, so the normal here
is the row, the Riesz representative of the functional `P.A i`, divided by its length. It points
out of the polytope; the reflection `d - 2 (d, s) s` does not see the sign.

## References

* [1] B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control
      and optimization". In Proc. of the 19th IFAC World Congress, Cape Town, South Africa,
      IFAC Proceedings Volumes 47(3), pp. 6123-6128, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The unit outward normal of the `i`-th inequality: its row `aᵢ`, normalized. -/
noncomputable def HPolytope.facetNormal (P : HPolytope E) (i : Fin P.m) : E :=
  -- the row `aᵢ` of `[1, Eq. 1]`, with `(aᵢ, x) = P.A i x`
  let a : E := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap (P.A i))
  ‖a‖⁻¹ • a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
