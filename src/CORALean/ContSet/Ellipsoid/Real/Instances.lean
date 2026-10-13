module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsequalConstruct
public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.ContSet.Definitions.CompactSet
public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Convex
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MapExact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MtimesExact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.PlusOuter
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfPointMem

@[expose] public section

/-!
# What `Ellipsoid` instantiates

`ContSet` and `Mtimes` by instance search, `OfPoint` at the degenerate case —
`G` with no columns — and `Plus` only once a caller has named the parameter it
carries. Otherwise closed under a linear image alone: a Minkowski sum of two
ellipsoids is not one, nor is a `linComb`. `Reduce` is the identity, as CORA's
`reduce` body is empty.

`Ellipsoid.plus_outer` holds at a fixed pair of scalings for every pair of
ellipsoids, so fixing `s₁` and `s₂` — with the inequality they owe — yields a
lawful `Plus`. It is a `def` and not an `instance` on purpose: instance search
must not make a precision choice, so a caller writes
`letI := Ellipsoid.plusInstance hne₁ hne₂ hs`, fixing the pair for a whole
run, where the tightest depends on the operands and the direction; per-call
precision names `Ellipsoid.plus` instead.

At `Vec ℝ n` only: an ellipsoid is described by a Euclidean norm, which a
general real module has none of.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (Ellipsoid n) (Vec ℝ n) := ⟨Ellipsoid.construct⟩

instance : ConvexSet (Ellipsoid n) (Vec ℝ n) := ⟨Ellipsoid.convex_construct⟩

instance : CompactSet (Ellipsoid n) (Vec ℝ n) := ⟨Ellipsoid.isCompact_construct⟩

instance : OfPoint (Ellipsoid n) (Vec ℝ n) where
  ofPoint := Ellipsoid.ofPoint
  mem_ofPoint := Ellipsoid.mem_ofPoint

/-- CORA's `@ellipsoid/reduce` has an empty body and returns its input, so this does nothing:
no order to reduce to, and the identity is a sound enclosure of itself. -/
instance : Reduce (Ellipsoid n) (Vec ℝ n) where
  reduce E _ := E
  reduce_outer _ _ := subset_rfl

/-- `Plus` at two scalings the caller chooses, with the inequality that makes
them sound. Deliberately not an `instance`: picking the pair is a precision
decision and instance search may not make one. -/
@[reducible] noncomputable def Ellipsoid.plusInstance {s₁ s₂ : ℝ} (hne₁ : s₁ ≠ 0)
    (hne₂ : s₂ ≠ 0) (hs : 1 / s₁ ^ 2 + 1 / s₂ ^ 2 ≤ 1) :
    ∀ n, Plus (Ellipsoid n) (Vec ℝ n) := fun _ =>
  { plus := Ellipsoid.plus s₁ s₂
    plus_outer := fun E₁ E₂ => Ellipsoid.plus_outer s₁ s₂ E₁ E₂ hne₁ hne₂ hs }

instance : Mtimes (Mat ℝ) (fun n => Ellipsoid n) where
  mtimes := Ellipsoid.mtimes
  mtimes_outer M E := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (Ellipsoid.mtimes_exact M E).subset

/-- `map_exact` carries no hypothesis at all — a generator matrix has no rank
condition to preserve — so a reindexing needs no more than any other map does. -/
noncomputable instance : Reindex (fun n => Ellipsoid n) where
  reindex e E := Ellipsoid.map (reindexLin e) E
  reindex_exact e E := (Ellipsoid.map_exact (reindexLin e) E).symm

/-- `Ellipsoid.isequal`, structural at tolerance `0`: sound, not exact. -/
instance : Isequal (Ellipsoid n) where
  isequal := Ellipsoid.isequal
  isequal_construct _ _ := Ellipsoid.isequal_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
