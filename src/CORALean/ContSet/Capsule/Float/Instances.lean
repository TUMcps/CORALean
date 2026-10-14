module

public import CORALean.ContSet.Capsule.Float.Theorems.Basic
public import CORALean.ContSet.Capsule.Float.Theorems.IsDisjointSound
public import CORALean.ContSet.Capsule.Float.Theorems.PlusOuter
public import CORALean.ContSet.Capsule.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Capsule.Float.Theorems.ConvHullOuter
public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.ContSet.Definitions.CompactSet

@[expose] public section

/-!
# What a float `Capsule` instantiates

`ConvexSet` and `CompactSet`, from the theorems that say so, then `Reduce` (the identity, as CORA's
empty body) and `Reindex` (CORA's `lift_` at a permutation). `ContSet` is in `Capsule`.
`Plus` and `Mtimes` take 100 Newton steps for their roots (`Capsule.plus`,
`Capsule.mtimes`; more steps buy accuracy only). As over ℝ, no `LinComb`: a capsule is closed
under almost nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ConvexSet (Capsule 𝕋 n) (Vec ℝ n) := ⟨Capsule.convex_construct⟩

instance : CompactSet (Capsule 𝕋 n) (Vec ℝ n) := ⟨Capsule.isCompact_construct⟩

instance : Reduce (Capsule 𝕋 n) (Vec ℝ n) where
  reduce := Capsule.reduce
  reduce_outer := Capsule.reduce_outer

instance : Reindex (Capsule 𝕋) where
  reindex := Capsule.reindex
  reindex_exact := Capsule.reindex_exact

/-- 100 Newton steps: from the start `(a + 1)/2` the iteration halves until it is near the root,
which takes about `log₂ √a` steps, then converges quadratically. -/
instance : Plus (Capsule 𝕋 n) (Vec ℝ n) where
  plus := Capsule.plus 100
  plus_outer := Capsule.plus_outer 100

/-- CORA's `convHull_`, 100 Newton steps as for `Plus`. -/
instance : LinComb (Capsule 𝕋 n) (Vec ℝ n) where
  linComb := Capsule.convHull 100
  linComb_outer := Capsule.convHull_outer 100

/-- CORA's `isIntersecting_` of two capsules, one-sidedly, 100 Newton steps as for `Plus`. -/
instance : IsDisjoint (Capsule 𝕋 n) (Capsule 𝕋 n) where
  isDisjoint := Capsule.isDisjoint 100
  isDisjoint_sound _ _ h := (Capsule.isDisjoint_sound 100 h).symm

instance : Mtimes (Mat 𝕋) (Capsule 𝕋) where
  mtimes M C := Capsule.mtimes 100 M C
  mtimes_outer M C := by
    simp only [ContSet.construct_mat, Set.biUnion_singleton]
    exact Capsule.mtimes_outer 100 M C

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
