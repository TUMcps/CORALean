module

public import CORALean.ContSet.Polygon.Real.Operations.Basic
public import CORALean.ContSet.Polygon.Real.Operations.OfPieces
public import CORALean.ContSet.Polygon.Real.Operations.SplitIntoConvexSets
public import CORALean.ContSet.Polygon.Real.Operations.Times
public import CORALean.ContSet.Polygon.Real.Theorems.IsCompact
public import CORALean.ContSet.Polygon.Real.Theorems.MtimesExact
public import CORALean.ContSet.VPolytope.Real.Instances
public import CORALean.ContSet.VPolytope.Real.Theorems.Convex

@[expose] public section

/-!
# `ContSet/Polygon/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix


-- ================================  `Polygon.isBounded_toSet`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `polygon/isBounded` returns `true`. -/
theorem Polygon.isBounded_toSet (P : Polygon) :
    Bornology.IsBounded (ContSetLike.toSet P) :=
  (Polygon.isCompact_toSet P).isBounded


-- ===========================  `Polygon.splitIntoConvexSets_exact`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Exactly: every returned set is convex and their union is the region. -/
theorem Polygon.splitIntoConvexSets_exact (P : Polygon) :
    (∀ p ∈ Polygon.splitIntoConvexSets P, Convex ℝ (VPolytope.toSet p)) ∧
      (⋃ p ∈ Polygon.splitIntoConvexSets P, VPolytope.toSet p) = ContSetLike.toSet P :=
  ⟨fun p _ => p.convex_toSet, rfl⟩


-- ==================================  `Polygon.times_exact`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `mtimes_exact` at the diagonal matrix: the image of the polygon under `x ↦ (v i * x i)`. -/
theorem Polygon.times_exact (v : Vec ℝ 2) (P : Polygon) :
    (diagonal v *ᵥ ·) '' ContSetLike.toSet P = ContSetLike.toSet (Polygon.times v P) :=
  Polygon.mtimes_exact (diagonal v) P


-- ==================================  `Polygon.toSet_empty`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Polygon.empty` is the empty set -/
theorem Polygon.toSet_empty :
    ContSetLike.toSet Polygon.empty = (∅ : Set (Vec ℝ 2)) := by
  ext x
  simp [SetUnion.mem_toSet, Polygon.empty]


-- =================================  `Polygon.toSet_ofPieces`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The constructor's denotation: the union of the pieces' vertex hulls. -/
theorem Polygon.toSet_ofPieces (pieces : List (VPolytope (Vec ℝ 2))) :
    ContSetLike.toSet (Polygon.ofPieces pieces) = ⋃ p ∈ pieces, VPolytope.toSet p := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
