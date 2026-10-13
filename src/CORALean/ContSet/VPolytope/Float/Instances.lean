import CORALean.ContSet.VPolytope.Float.Theorems.IntersectionOuter
import CORALean.ContSet.VPolytope.Float.Theorems.LinCombOuter
import CORALean.ContSet.VPolytope.Float.Theorems.MtimesOuter
import CORALean.ContSet.VPolytope.Float.Theorems.PlusOuter

/-!
# What the float `VPolytope` instantiates

`Plus`, `LinComb`, `Reduce` — the identity again — and `Mtimes`, as the exact
layer's. `ContSet` comes from `InflatedContSet` and is not declared here.

`Intersection` too, and needs no direction family here: it goes through the float box's
own exact `intersection`, unlike the exact layer's, which must be handed one. No
`OfPoint`: it would round a real point into `𝕋`, an operation this layer lacks.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : Plus (VPolytope (Vec 𝕋 n)) (Vec ℝ n) where
  plus P₁ P₂ := (VPolytope.plus P₁ P₂).materialise
  plus_outer P₁ P₂ := by
    rw [VPolytope.materialise_eq]
    exact VPolytope.plus_outer P₁ P₂

instance : Intersection (VPolytope (Vec 𝕋 n)) (Vec ℝ n) where
  intersection P₁ P₂ := (VPolytope.intersection P₁ P₂).materialise
  intersection_outer P₁ P₂ := by
    rw [VPolytope.materialise_eq]
    exact VPolytope.intersection_outer P₁ P₂

instance : LinComb (VPolytope (Vec 𝕋 n)) (Vec ℝ n) where
  linComb P₁ P₂ := (VPolytope.linComb P₁ P₂).materialise
  linComb_outer P₁ P₂ := by
    rw [VPolytope.materialise_eq]
    exact VPolytope.linComb_outer P₁ P₂

-- `reduce` is the identity: a vertex list has no ranking to run
instance : Reduce (VPolytope (Vec 𝕋 n)) (Vec ℝ n) where
  reduce P _ := P.materialise
  reduce_outer P _ := by
    rw [VPolytope.materialise_eq]

instance : Mtimes (Mat 𝕋) (fun k => VPolytope (Vec 𝕋 k)) where
  mtimes M P := (VPolytope.mtimes M P).materialise
  mtimes_outer M P := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, VPolytope.materialise_eq]
    exact VPolytope.mtimes_outer M P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
