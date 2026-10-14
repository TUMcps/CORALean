module

public import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.ReduceOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.ReindexExact
public import CORALean.ContSet.Interval.Float.Instances

@[expose] public section

/-!
# What the float `ConZonotope` instantiates

The operation classes `Plus`, `LinComb`, `Intersection`, `Reduce` and `Mtimes`, then
`Reindex`, which is exact. `Intersection` is outer here where the exact layer's is
exact: the agreement rows' right-hand side is an interval rounded outward.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   02-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : Plus (ConZonotope 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  plus C₁ C₂ := (C₁.plus C₂).materialise
  plus_outer C₁ C₂ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.plus_outer C₁ C₂

instance : LinComb (ConZonotope 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  linComb cZ₁ cZ₂ := (ConZonotope.linComb cZ₁ cZ₂).materialise
  linComb_outer cZ₁ cZ₂ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.linComb_outer cZ₁ cZ₂

instance : Intersection (ConZonotope 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  intersection cZ₁ cZ₂ := (cZ₁.intersection cZ₂).materialise
  intersection_outer cZ₁ cZ₂ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.intersection_outer cZ₁ cZ₂

instance : Reduce (ConZonotope 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  reduce cZ o := (ConZonotope.reduce cZ o).materialise
  reduce_outer cZ o := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.reduce_outer cZ o

/-- Exact, alone among the fields here: a relabelling moves stored floats and
computes nothing, so the error box is carried across rather than grown. -/
instance : Reindex (fun k => ConZonotope 𝕋 (Vec 𝕋 k)) where
  reindex e cZ := (ConZonotope.reindex e cZ).materialise
  reindex_exact e cZ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.reindex_exact e cZ

instance : Mtimes (Mat 𝕋) (fun k => ConZonotope 𝕋 (Vec 𝕋 k)) where
  mtimes M cZ := (ConZonotope.mtimes M cZ).materialise
  mtimes_outer M cZ := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, ConZonotope.materialise_eq]
    exact ConZonotope.mtimes_outer M cZ

/-- The same operation at a float interval matrix, as `Zonotope`'s is. -/
instance : Mtimes ℐ[𝕋] (fun k => ConZonotope 𝕋 (Vec 𝕋 k)) where
  mtimes IM cZ := (ConZonotope.mtimesIntervalMat IM cZ).materialise
  mtimes_outer IM cZ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.mtimesIntervalMat_outer IM cZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
