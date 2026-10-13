import CORALean.ContSet.Polygon.Real.Theorems.IsCompact
import CORALean.ContSet.Polygon.Real.Theorems.LinCombOuter
import CORALean.ContSet.VPolytope.Real.Instances

/-!
# What `Polygon` instantiates

`ContSet`, `Plus` and `Reduce` come from `SetUnion` at the member `VPolytope (Vec ℝ 2)`;
`Mtimes` too, at the family `fun n => VPolytope (Vec ℝ n)`, at the `Mat ℝ` of any size.
`LinComb` is this layer's own, as `SetUnion` has none, and `CompactSet` is `isCompact_construct`
at the one-field class.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  INSTANCES  ========================================= --

instance : LinComb Polygon (Vec ℝ 2) where
  linComb := Polygon.linComb
  linComb_outer := Polygon.linComb_outer

instance : CompactSet Polygon (Vec ℝ 2) :=
  ⟨Polygon.isCompact_construct⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
