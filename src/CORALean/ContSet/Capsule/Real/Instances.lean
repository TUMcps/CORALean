import CORALean.ContSet.Capsule.Real.Theorems.IsequalConstruct
import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.ContSet.Definitions.CompactSet
import CORALean.ContSet.Capsule.Real.Theorems.API
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# What `Capsule` instantiates

`ContSet`, `ConvexSet`, `CompactSet`, `OfPoint` at `g = 0`, `r = 0`, `Reduce` as the identity, as
CORA's empty `reduce` body is, `Reindex`, CORA's `lift_` at a permutation, and the two outer
operations `Plus` and `Mtimes`.

A capsule is closed under almost nothing, so `Plus` and `Mtimes` are enclosures, not exact. The
Minkowski sum of two capsules is not a capsule (a segment thickened by two balls is not a ball),
and an affine image of one is a segment thickened by an *ellipsoid*, since a linear map need not
preserve the Euclidean ball; CORA absorbs the shorter generator and the ellipsoid into a larger
radius. `LinComb` is CORA's `convHull_`, also an enclosure: the hull of two capsules is no
capsule.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (Capsule n) (Vec ℝ n) := ⟨Capsule.construct⟩

instance : ConvexSet (Capsule n) (Vec ℝ n) := ⟨Capsule.convex_construct⟩

instance : CompactSet (Capsule n) (Vec ℝ n) := ⟨Capsule.isCompact_construct⟩

instance : OfPoint (Capsule n) (Vec ℝ n) where
  ofPoint := Capsule.ofPoint
  mem_ofPoint := Capsule.mem_ofPoint

/-- CORA's `@capsule/reduce` has an empty body and returns its input: there is no order to reduce
to, so doing nothing is the sound answer and the one CORA gives. -/
instance : Reduce (Capsule n) (Vec ℝ n) where
  reduce C _ := C
  reduce_outer _ _ := subset_rfl

/-- `Capsule.reindex`, CORA's `lift_` at a permutation of the coordinates; the one case CORA
defines. -/
instance : Reindex (fun n => Capsule n) where
  reindex := Capsule.reindex
  reindex_exact e C := Capsule.reindex_exact e C

/-- CORA's capsule-plus-capsule, the shorter generator absorbed into the radius. -/
noncomputable instance : Plus (Capsule n) (Vec ℝ n) where
  plus := Capsule.plus
  plus_outer := Capsule.plus_outer

/-- CORA's `mtimes`, with the radius scaled by the Frobenius bound of the operator norm, not by
CORA's `max(eig(M Mᵀ))`, the square of it (see `Capsule.mtimes_cora_counterexample`). -/
noncomputable instance : Mtimes (Mat ℝ) (fun n => Capsule n) where
  mtimes := Capsule.mtimes
  mtimes_outer M C := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Capsule.mtimes_outer M C

/-- CORA's `convHull_`, a ball around the segment between the two centres. -/
noncomputable instance : LinComb (Capsule n) (Vec ℝ n) where
  linComb := Capsule.convHull
  linComb_outer := Capsule.convHull_outer

/-- `Capsule.isequal`, structural at tolerance `0`: sound, not exact. -/
instance : Isequal (Capsule n) where
  isequal := Capsule.isequal
  isequal_construct _ _ := Capsule.isequal_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
