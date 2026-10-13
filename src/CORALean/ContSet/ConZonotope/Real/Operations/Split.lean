import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_ConZonotope
import CORALean.ContSet.Interval.Real.Operations.SplitAt

/-!
# `ConZonotope.split`

CORA's `@conZonotope/split` along one dimension `d`: take the box `I` around the set, cut it at
the middle of its `d`-th side into `I₁ = [inf, mid]` and `I₂ = [mid, sup]` there, and intersect
the set with each, `and_(cZ, I, 'exact')`, which converts the box to a constrained zonotope.
A pair, as CORA returns both halves at once.

CORA's call without a dimension is this at every `d`, returned as a cell of pairs; that is the
map `d ↦ split cZ d` and is not a separate definition.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The part of `cZ` below and the part above the middle of its box along dimension `d`. -/
noncomputable def ConZonotope.split (cZ : ConZonotope (Vec ℝ n)) (d : Fin n) :
    ConZonotope (Vec ℝ n) × ConZonotope (Vec ℝ n) :=
  let I := cZ.interval
  -- the box cut at the middle of side `d`, `[inf, mid]` and `[mid, sup]` there
  let (I₁, I₂) := I.splitAt d
  (cZ.intersection I₁.conZonotope, cZ.intersection I₂.conZonotope)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
