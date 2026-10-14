module

public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.ConZonotope.Real.Operations.Project
public import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage
public import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompact
public import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact

@[expose] public section

/-!
# `ContSet/ConZonotope/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix

variable {n m : ℕ} {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =============================  `ConZonotope.isClosed_construct`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---

/-- Read off compactness. The halfspace description behind `domain` is closed on its
own, but `construct` is an image of it, and an image of a merely closed set need
not be closed. -/
theorem ConZonotope.isClosed_construct (cZ : ConZonotope α) : IsClosed cZ.construct :=
  cZ.isCompact_construct.isClosed


-- ================================  `ConZonotope.mtimes_exact`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---

/-- `map_exact` at `A *ᵥ ·`, which is the case reachability runs: the constraints
are on the coefficients and a linear map of the ambient space never sees them. -/
theorem ConZonotope.mtimes_exact {n m : ℕ} (M : Mat ℝ m n) (cZ : ConZonotope (Vec ℝ n)) :
    (M *ᵥ ·) '' cZ.construct = (ConZonotope.mtimes M cZ).construct :=
  ConZonotope.map_exact (Matrix.mulVecLin M) cZ


-- ===============================  `ConZonotope.project_exact`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Reading the same coordinates of every member, no hypothesis on `dims`: a linear map is exact
without injectivity, so nothing is added and nothing lost. -/
theorem ConZonotope.project_exact (cZ : ConZonotope (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' cZ.construct = (cZ.project dims).construct :=
  ConZonotope.map_exact (LinearMap.funLeft ℝ ℝ dims) cZ

end CORALean.Real


namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ==========================  `ConZonotope.representsa_emptySet_iff`  ========================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A constrained zonotope is empty iff its coefficient polytope is -/
theorem ConZonotope.representsa_emptySet_iff (cZ : ConZonotope α) :
    cZ.construct = ∅ ↔ cZ.representsa_emptySet := by
  rw [ConZonotope.construct_eq_image, ConZonotope.representsa_emptySet]
  exact Set.image_eq_empty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
