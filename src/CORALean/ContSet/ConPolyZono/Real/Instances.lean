import CORALean.ContSet.ContSet.CompactSet
import CORALean.ContSet.ConPolyZono.Real.Theorems.AndExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.IsCompact
import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.MtimesExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.OfPointMem
import CORALean.ContSet.ConPolyZono.Real.Theorems.PlusExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceOuter

/-!
# What `ConPolyZono` instantiates

`ContSet`, `CompactSet`, `Plus`, `Mtimes`, `Reduce`, `And` and `OfPoint`, each obligation
a theorem from `Theorems` read in the `⊆` direction.

No `ConvexSet`: the sets are generally not convex, which is the point of the
representation. `CompactSet` holds all the same, and on the constraints rather
than in spite of them — a constraint row is a polynomial in the factors, so it
cuts the coefficient cube down to a closed subset of it.

`Reduce` ranks both generator blocks together and boxes what it drops, leaving
the constraint block alone; `compact`, which it runs first, is what bounds the
constraint counts. No `LinComb`: it would have to relax the independent block as
`PolyZonotope`'s does, and nothing here is faked.

`quadMap` alone has no class to instantiate, so a caller names
`ConPolyZono.quadMap` directly — the one operation `And` (#10) does not cover.
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

instance : ContSet (ConPolyZono α) α := ⟨ConPolyZono.construct⟩

/-- At every ambient type, as the set-level statement is: it is the coefficient
space that has to be finite-dimensional, and that one is `Fin p × Fin q`. -/
instance {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] : CompactSet (ConPolyZono α) α :=
  ⟨ConPolyZono.isCompact_construct⟩

instance : Plus (ConPolyZono α) α where
  plus := ConPolyZono.plus
  plus_outer cPZ₁ cPZ₂ := (ConPolyZono.plus_exact cPZ₁ cPZ₂).subset

instance : OfPoint (ConPolyZono α) α where
  ofPoint := ConPolyZono.ofPoint
  mem_ofPoint := ConPolyZono.mem_ofPoint

instance : And (ConPolyZono (Vec ℝ n)) (Vec ℝ n) where
  and := ConPolyZono.and
  and_outer cPZ₁ cPZ₂ := (ConPolyZono.and_exact cPZ₁ cPZ₂).subset

/-- Pinned to `Vec`, as `PolyZonotope`'s is: a generator ranking and the box that
absorbs what it drops are both entrywise. -/
noncomputable instance : Reduce (ConPolyZono (Vec ℝ n)) (Vec ℝ n) where
  reduce := ConPolyZono.reduce
  reduce_outer := ConPolyZono.reduce_outer

instance : Mtimes (Mat ℝ) (fun n => ConPolyZono (Vec ℝ n)) where
  mtimes := ConPolyZono.mtimes
  mtimes_outer M cPZ := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (ConPolyZono.mtimes_exact M cPZ).subset

/-- The constrained-polynomial-zonotope family over vectors. The elaborator
cannot read the family off one member, so a use site names it: `(S := 𝒞𝒫𝒵)`. -/
scoped notation "𝒞𝒫𝒵" => fun n => ConPolyZono (Vec ℝ n)

instance : Reindex 𝒞𝒫𝒵 where
  reindex e cPZ := ConPolyZono.map (reindexLin e) cPZ
  reindex_exact e cPZ := (ConPolyZono.map_exact (reindexLin e) cPZ).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
