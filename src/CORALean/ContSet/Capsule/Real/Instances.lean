import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.ContSet.Definitions.CompactSet
import CORALean.ContSet.Capsule.Real.Theorems.API
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# What `Capsule` instantiates

`ContSet`, `ConvexSet`, `CompactSet`, `OfPoint` at `g = 0`, `r = 0`, `Reduce` as the identity, as
CORA's empty `reduce` body is, and `Reindex`, CORA's `lift_` at a permutation.

No `Plus`, `Mtimes`, or `LinComb`: a capsule is closed under almost nothing.
The Minkowski sum of two capsules is not a capsule (a segment thickened by two
balls is not a ball), and an affine image of one is a segment thickened by an
*ellipsoid*, since a linear map need not preserve the Euclidean ball. That is
why CORA reaches for a capsule to describe an obstacle rather than to carry a
reachable set through an operation.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
