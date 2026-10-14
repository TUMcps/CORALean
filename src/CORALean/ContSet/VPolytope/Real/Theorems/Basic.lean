module

public import CORALean.ContSet.VPolytope.Real.Operations.Basic
public import CORALean.ContSet.VPolytope.Real.Operations.Or
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvHullExact
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.VPolytope.Real.Theorems.MapExact
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice

@[expose] public section

/-!
# `ContSet/VPolytope/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =============================  `VPolytope.enclosePoints_exact`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- An equality, not an enclosure: the polytope is the smallest convex set containing the points. -/
theorem VPolytope.enclosePoints_exact {N : ℕ} (pts : Fin N → Vec ℝ n) :
    (VPolytope.enclosePoints pts).construct = convexHull ℝ (Set.range pts) :=
  VPolytope.construct_eq_convexHull _

end CORALean.Real


-- =============================  `VPolytope.isCompact_construct`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

/-- The hull of a finite set. A halfspace description is closed too but need not be
bounded, which is why the two get separate proofs rather than one. -/
theorem VPolytope.isCompact_construct (P : VPolytope α) : IsCompact P.construct := by
  rw [VPolytope.construct_eq_convexHull]
  exact Set.Finite.isCompact_convexHull ℝ (Set.finite_range P.V)

end CORALean.Real


-- =============================  `VPolytope.isBounded_construct`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

/-- Read off compactness. This is what a halfspace description cannot have: it
admits unbounded sets, which is the difference between the two representations. -/
theorem VPolytope.isBounded_construct (P : VPolytope α) : Bornology.IsBounded P.construct :=
  P.isCompact_construct.isBounded

end CORALean.Real


-- ==============================  `VPolytope.isClosed_construct`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]

/-- Read off compactness. A halfspace description proves its own closedness
directly, having no compactness to read it off. -/
theorem VPolytope.isClosed_construct (P : VPolytope α) : IsClosed P.construct :=
  P.isCompact_construct.isClosed

end CORALean.Real


-- ==============================  `VPolytope.matPolytope_exact`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- The matrices of `matPolytope P` are exactly the vectors of `P` read as columns. -/
theorem VPolytope.matPolytope_exact (P : VPolytope (Vec ℝ n)) :
    (fun v => (fun i _ => v i : Mat ℝ n 1)) '' P.construct = P.matPolytope.construct :=
  VPolytope.map_exact (colLin n) P

end CORALean.Real


-- ===================================  `VPolytope.or_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- The union of two polytopes is not a polytope in general, so `or` returns its hull; that hull is
exact, and contains the union. -/
theorem VPolytope.or_exact {α : Type} [AddCommGroup α] [Module ℝ α] (P Q : VPolytope α) :
    (P.or Q).construct = convexHull ℝ (P.construct ∪ Q.construct) :=
  VPolytope.convHull_exact P Q

end CORALean.Real


-- ================================  `VPolytope.project_exact`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n m : ℕ}

/-- Reading the same coordinates of every member, no hypothesis on `dims`: a linear map is exact
without injectivity, so nothing is added and nothing lost. -/
theorem VPolytope.project_exact (P : VPolytope (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' P.construct = (P.project dims).construct :=
  VPolytope.map_exact (LinearMap.funLeft ℝ ℝ dims) P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
