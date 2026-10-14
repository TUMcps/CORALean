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


-- ================================  `Polygon.construct_empty`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- `Polygon.empty` is the empty set -/
theorem Polygon.construct_empty :
    ContSet.construct Polygon.empty = (∅ : Set (Vec ℝ 2)) := by
  ext x
  simp [SetUnion.mem_construct, Polygon.empty]

end CORALean.Real


-- ===============================  `Polygon.construct_ofPieces`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- The constructor's denotation: the union of the pieces' vertex hulls. -/
theorem Polygon.construct_ofPieces (pieces : List (VPolytope (Vec ℝ 2))) :
    ContSet.construct (Polygon.ofPieces pieces) = ⋃ p ∈ pieces, VPolytope.construct p := rfl

end CORALean.Real


-- ==============================  `Polygon.isBounded_construct`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- CORA's `polygon/isBounded` returns `true`. -/
theorem Polygon.isBounded_construct (P : Polygon) :
    Bornology.IsBounded (ContSet.construct P) :=
  (Polygon.isCompact_construct P).isBounded

end CORALean.Real


-- ===========================  `Polygon.splitIntoConvexSets_exact`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- Exactly: every returned set is convex and their union is the region. -/
theorem Polygon.splitIntoConvexSets_exact (P : Polygon) :
    (∀ p ∈ Polygon.splitIntoConvexSets P, Convex ℝ (VPolytope.construct p)) ∧
      (⋃ p ∈ Polygon.splitIntoConvexSets P, VPolytope.construct p) = ContSet.construct P :=
  ⟨fun p _ => p.convex_construct, rfl⟩

end CORALean.Real


-- ==================================  `Polygon.times_exact`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

/-- `mtimes_exact` at the diagonal matrix: the image of the polygon under `x ↦ (v i * x i)`. -/
theorem Polygon.times_exact (v : Vec ℝ 2) (P : Polygon) :
    (diagonal v *ᵥ ·) '' ContSet.construct P = ContSet.construct (Polygon.times v P) :=
  Polygon.mtimes_exact (diagonal v) P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
