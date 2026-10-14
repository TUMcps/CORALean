module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.IsequalConstruct
public import CORALean.ContSet.ContSet.Definitions.CompactSet
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Theorems.IsCompact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceOuter

@[expose] public section

/-!
# What `PolyZonotope` instantiates

Each obligation is a theorem from `Theorems`, the exact ones read in the `⊆`
direction.

`Plus`, `LinComb` and `OfPoint` sit at every ambient type rather than at `Vec`: none needs
coordinates. `Reduce` pins down `Vec`, as `Zonotope`'s does, since a generator ranking and a box are
both entrywise. `Mtimes` moves between dimensions at a plain matrix and, as `Zonotope` also carries,
at an interval one. `quadMap` has no class, so a caller names `PolyZonotope.quadMap`.

`Reduce`'s one number bounds both generator blocks together, as the class
field's `o` does everywhere else; the class carries only the enclosure.
`reduceDependent` is the tighter rule and deliberately not the instance: it
bounds no count, so an algorithm reaching it through `Reduce` would grow.

Noncomputable, twice over: `compact` decides whether a generator of a real
module is zero, and the ranking orders reals.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}

/-- The polynomial-zonotope family over vectors. The elaborator cannot read the
family off one member, so a use site names it: `(S := 𝒫𝒵)` — two letters, `𝒫`
alone being Mathlib's powerset. -/
scoped notation "𝒫𝒵" => fun n => PolyZonotope (Vec ℝ n)


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (PolyZonotope α) α := ⟨PolyZonotope.construct⟩

/-- Compact, not convex: the set is the image of a cube under a polynomial. -/
instance {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] : CompactSet (PolyZonotope α) α :=
  ⟨PolyZonotope.isCompact_construct⟩

instance : Plus (PolyZonotope α) α where
  plus := PolyZonotope.plus
  plus_outer pZ₁ pZ₂ := (PolyZonotope.plus_exact pZ₁ pZ₂).subset

instance : OfPoint (PolyZonotope α) α where
  ofPoint := PolyZonotope.ofPoint
  mem_ofPoint := PolyZonotope.mem_ofPoint

noncomputable instance : LinComb (PolyZonotope α) α where
  linComb := PolyZonotope.linComb
  linComb_outer := PolyZonotope.linComb_outer

noncomputable instance : Reduce (PolyZonotope (Vec ℝ n)) (Vec ℝ n) where
  reduce := PolyZonotope.reduce
  reduce_outer := PolyZonotope.reduce_outer

instance : Mtimes (Mat ℝ) (𝒫𝒵) where
  mtimes := PolyZonotope.mtimes
  mtimes_outer M pZ := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (PolyZonotope.mtimes_exact M pZ).subset

/-- The same operation at an interval matrix: the radius is boxed into one fresh
*independent* generator per coordinate, unlike `Zonotope`, which has no other
block to keep it out of. -/
noncomputable instance : Mtimes ℐ 𝒫𝒵 where
  mtimes := PolyZonotope.mtimesIntervalMat
  mtimes_outer IM pZ := PolyZonotope.mtimesIntervalMat_outer IM pZ

instance : Reindex 𝒫𝒵 where
  reindex e pZ := PolyZonotope.map (reindexLin e) pZ
  reindex_exact e pZ := (PolyZonotope.map_exact (reindexLin e) pZ).symm

/-- `PolyZonotope.isequal`, structural at tolerance `0`: sound, not exact. -/
instance : Isequal (PolyZonotope α) where
  isequal := PolyZonotope.isequal
  isequal_construct _ _ := PolyZonotope.isequal_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
