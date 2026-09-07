import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceOuter

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

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (PolyZonotope α) α := ⟨PolyZonotope.construct⟩

instance : Plus (PolyZonotope α) α where
  plus := PolyZonotope.plus
  plus_outer PZ₁ PZ₂ := (PolyZonotope.plus_exact PZ₁ PZ₂).subset

instance : OfPoint (PolyZonotope α) α where
  ofPoint := PolyZonotope.ofPoint
  mem_ofPoint := PolyZonotope.mem_ofPoint

noncomputable instance : LinComb (PolyZonotope α) α where
  linComb := PolyZonotope.linComb
  linComb_outer := PolyZonotope.linComb_outer

noncomputable instance : Reduce (PolyZonotope (Vec ℝ n)) (Vec ℝ n) where
  reduce := PolyZonotope.reduce
  reduce_outer := PolyZonotope.reduce_outer

instance : Mtimes (Mat ℝ) (fun n => PolyZonotope (Vec ℝ n)) where
  mtimes := PolyZonotope.mtimes
  mtimes_outer M PZ := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (PolyZonotope.mtimes_exact M PZ).subset

/-- The polynomial-zonotope family over vectors. The elaborator cannot read the
family off one member, so a use site names it: `(S := 𝒫𝒵)` — two letters, `𝒫`
alone being Mathlib's powerset. -/
scoped notation "𝒫𝒵" => fun n => PolyZonotope (Vec ℝ n)

/-- The same operation at an interval matrix: the radius is boxed into one fresh
*independent* generator per coordinate, unlike `Zonotope`, which has no other
block to keep it out of. -/
noncomputable instance : Mtimes ℐ 𝒫𝒵 where
  mtimes := PolyZonotope.mtimesIntervalMat
  mtimes_outer IM PZ := PolyZonotope.mtimesIntervalMat_outer IM PZ

instance : Reindex 𝒫𝒵 where
  reindex e PZ := PolyZonotope.map (reindexLin e) PZ
  reindex_exact e PZ := (PolyZonotope.map_exact (reindexLin e) PZ).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
