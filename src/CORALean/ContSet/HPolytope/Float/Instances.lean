module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.IntersectionOuter

@[expose] public section

/-!
# What the float `HPolytope` instantiates

`ContSet` (through `InflatedContSet`), `Reduce` and `Intersection`, as over ℝ; the intersection
is an outer approximation, the boxes being folded into the rows first. Not `Plus`, `LinComb`
or `Mtimes`, though `plusOf`, `linCombOf` and `mtimesOf` all compute: closing over their
directions needs bounds for every polytope, and that oracle does not exist here.

`Reduce` is the identity, exactly as over ℝ: nothing here decides redundancy
among halfspaces, so keeping the description is the sound stand-in.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : Reduce (HPolytope 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  reduce P _ := P
  reduce_outer _ _ := subset_rfl

instance : Intersection (HPolytope 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  intersection := HPolytope.intersection
  intersection_outer P₁ P₂ := HPolytope.intersection_outer P₁ P₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
