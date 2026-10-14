module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReindexExact

@[expose] public section

/-!
# What `PolyZonotope` instantiates

`ContSet` is not among them — `InflatedContSet` supplies it, which is what makes
this the same class the exact layer instantiates.

`Reduce` is here and is *computable*, where the exact layer's instance is not:
`Tuple.sort` needs a `LinearOrder`, which no float type has lawfully, while
`sortPerm` asks its comparator for nothing. Soundness never depended on the
ranking — `reduceBy_outer` holds at every partition — so the free comparator
costs precision and nothing else. `LinComb` is computable here for the same
reason: over ℝ it is noncomputable only because `Reduce` in the same file is.

`compact` runs first, as over ℝ, so the count bounded is of distinct monomials.
It is the one operation weaker in kind than its exact counterpart: merging two
columns adds their entries, so it encloses where the exact one is an equality.

`quadMap` has no class to instantiate, as over ℝ, so a caller names
`PolyZonotope.quadMap`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The polynomial-zonotope family over vectors.
The scalar is an argument: a notation cannot capture the section
variable `𝕋`, so `(S := 𝒫𝒵[𝕋])`. -/
scoped notation "𝒫𝒵[" t "]" => fun n => PolyZonotope (Vec t n)


-- ========================================  INSTANCES  ========================================= --

instance {n : ℕ} : Plus (PolyZonotope (Vec 𝕋 n)) (Vec ℝ n) where
  plus pZ₁ pZ₂ := (pZ₁.plus pZ₂).materialise
  plus_outer pZ₁ pZ₂ := by
    rw [PolyZonotope.materialise_eq]
    exact PolyZonotope.plus_outer pZ₁ pZ₂

instance {n : ℕ} : LinComb (PolyZonotope (Vec 𝕋 n)) (Vec ℝ n) where
  linComb pZ₁ pZ₂ := (pZ₁.linComb pZ₂).materialise
  linComb_outer pZ₁ pZ₂ := by
    rw [PolyZonotope.materialise_eq]
    exact PolyZonotope.linComb_outer pZ₁ pZ₂

-- `reduce` is computable here, `sortPerm` asking its comparator for no laws
instance {n : ℕ} : Reduce (PolyZonotope (Vec 𝕋 n)) (Vec ℝ n) where
  reduce pZ o := (pZ.reduce o).materialise
  reduce_outer pZ o := by
    rw [PolyZonotope.materialise_eq]
    exact PolyZonotope.reduce_outer pZ o

instance : Mtimes (Mat 𝕋) 𝒫𝒵[𝕋] where
  mtimes M pZ := (PolyZonotope.mtimes M pZ).materialise
  mtimes_outer M pZ := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton, PolyZonotope.materialise_eq]
    exact PolyZonotope.mtimes_outer M pZ

/-- Exact, alone among the fields here: a relabelling moves stored floats and
computes nothing, so the error box is carried across rather than grown. -/
instance : Reindex 𝒫𝒵[𝕋] where
  reindex e pZ := (PolyZonotope.reindex e pZ).materialise
  reindex_exact e pZ := by
    rw [PolyZonotope.materialise_eq]
    exact PolyZonotope.reindex_exact e pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
