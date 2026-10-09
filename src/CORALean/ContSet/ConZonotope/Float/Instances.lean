import CORALean.ContSet.ConZonotope.Float.Theorems.API
import CORALean.ContSet.Interval.Float.Instances

/-!
# What the float `ConZonotope` instantiates

The operation classes `Plus`, `LinComb`, `Intersection`, `Reduce` and `Mtimes`, then
`Reindex`, which is exact. `Intersection` is outer here where the exact layer's is
exact: the agreement rows' right-hand side is an interval rounded outward.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   02-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : Plus (ConZonotope 𝕋 n) (Vec ℝ n) where
  plus C₁ C₂ := (C₁.plus C₂).materialise
  plus_outer C₁ C₂ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.plus_outer C₁ C₂

instance : LinComb (ConZonotope 𝕋 n) (Vec ℝ n) where
  linComb := ConZonotope.linComb
  linComb_outer := ConZonotope.linComb_outer

instance : Intersection (ConZonotope 𝕋 n) (Vec ℝ n) where
  intersection cZ₁ cZ₂ := (cZ₁.intersection cZ₂).materialise
  intersection_outer cZ₁ cZ₂ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.intersection_outer cZ₁ cZ₂

instance : Reduce (ConZonotope 𝕋 n) (Vec ℝ n) where
  reduce := ConZonotope.reduce
  reduce_outer := ConZonotope.reduce_outer

/-- Exact, alone among the fields here: a relabelling moves stored floats and
computes nothing, so the error box is carried across rather than grown. -/
instance : Reindex (ConZonotope 𝕋) where
  reindex e cZ := (ConZonotope.reindex e cZ).materialise
  reindex_exact e cZ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.reindex_exact e cZ

instance : Mtimes (Mat 𝕋) (ConZonotope 𝕋) where
  mtimes M cZ := (ConZonotope.mtimes M cZ).materialise
  mtimes_outer M cZ := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, ConZonotope.materialise_eq]
    exact ConZonotope.mtimes_outer M cZ

/-- The same operation at a float interval matrix, as `Zonotope`'s is. -/
instance : Mtimes (fun m n => Interval (Mat 𝕋 m n)) (ConZonotope 𝕋) where
  mtimes IM cZ := (ConZonotope.mtimesIntervalMat IM cZ).materialise
  mtimes_outer IM cZ := by
    rw [ConZonotope.materialise_eq]
    exact ConZonotope.mtimesIntervalMat_outer IM cZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
