module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.LinCombOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MtimesOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.PlusOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ReduceOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ReindexExact

@[expose] public section

/-!
# What `ConPolyZono` instantiates

`Plus`, `LinComb`, `Mtimes`, `Reduce` and `Intersection`, as over ℝ. `ContSet` is not among them —
`InflatedContSet` supplies it, which is what makes this the same class the exact
layer instantiates.

`Reduce` is *computable* here where the exact layer's instance is not:
`Tuple.sort` needs a `LinearOrder`, which no float type has lawfully, while
`sortPerm` asks its comparator for nothing. Soundness never depended on the
ranking — `reduceBy_outer` holds at every partition — so the free comparator
costs precision and nothing else. No `CompactSet`, as at no other float
representation: compactness is a statement about the exact specification.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  INSTANCES  ========================================= --

instance {n : ℕ} : Plus (ConPolyZono 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  plus cPZ₁ cPZ₂ := (cPZ₁.plus cPZ₂).materialise
  plus_outer cPZ₁ cPZ₂ := by
    rw [ConPolyZono.materialise_eq]
    exact ConPolyZono.plus_outer cPZ₁ cPZ₂

instance {n : ℕ} : LinComb (ConPolyZono 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  linComb cPZ₁ cPZ₂ := (cPZ₁.linComb cPZ₂).materialise
  linComb_outer cPZ₁ cPZ₂ := by
    rw [ConPolyZono.materialise_eq]
    exact ConPolyZono.linComb_outer cPZ₁ cPZ₂

-- `reduce` is computable here, `sortPerm` asking its comparator for no laws
instance {n : ℕ} : Reduce (ConPolyZono 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  reduce cPZ o := (cPZ.reduce o).materialise
  reduce_outer cPZ o := by
    rw [ConPolyZono.materialise_eq]
    exact ConPolyZono.reduce_outer cPZ o

instance {n : ℕ} : Intersection (ConPolyZono 𝕋 (Vec 𝕋 n)) (Vec ℝ n) where
  intersection cPZ₁ cPZ₂ := (ConPolyZono.intersection cPZ₁ cPZ₂).materialise
  intersection_outer cPZ₁ cPZ₂ := by
    rw [ConPolyZono.materialise_eq]
    exact ConPolyZono.intersection_outer cPZ₁ cPZ₂

instance : Mtimes (Mat 𝕋) (fun k => ConPolyZono 𝕋 (Vec 𝕋 k)) where
  mtimes M cPZ := (ConPolyZono.mtimes M cPZ).materialise
  mtimes_outer M cPZ := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, ConPolyZono.materialise_eq]
    exact ConPolyZono.mtimes_outer M cPZ

/-- Exact, alone among the fields here: a relabelling moves stored floats and
computes nothing, so the error box is carried across rather than grown. -/
instance : Reindex (fun k => ConPolyZono 𝕋 (Vec 𝕋 k)) where
  reindex e cPZ := (ConPolyZono.reindex e cPZ).materialise
  reindex_exact e cPZ := by
    rw [ConPolyZono.materialise_eq]
    exact ConPolyZono.reindex_exact e cPZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
