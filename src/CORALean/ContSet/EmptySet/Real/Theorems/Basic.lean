module

public import CORALean.ContSet.ContSet.Definitions.IsFullDim
public import CORALean.ContSet.EmptySet.Real.Instances
public import CORALean.ContSet.EmptySet.Real.Operations.Basic
public import CORALean.ContSet.EmptySet.Real.Operations.HPolytope
public import CORALean.ContSet.EmptySet.Real.Operations.IsBounded
public import CORALean.ContSet.EmptySet.Real.Operations.Not
public import CORALean.ContSet.Fullspace.Real.Instances
public import CORALean.ContSet.HPolytope.Real.Operations.ConstructEmptySet
public import CORALean.ContSet.Interval.Real.Theorems.EmptyExact
public import CORALean.ContSet.VPolytope.Real.Operations.ConstructEmptySet
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `ContSet/EmptySet/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- ================================  `EmptySet.construct_empty`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `EmptySet.empty` denotes `∅` -/
theorem EmptySet.construct_empty : construct (EmptySet.empty n) = (∅ : Set (Vec ℝ n)) := rfl


-- ================================  `EmptySet.hPolytope_exact`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `EmptySet.hPolytope` denotes the empty set -/
theorem EmptySet.hPolytope_exact (E : EmptySet n) :
    E.hPolytope.construct = construct E :=
  HPolytope.construct_emptySet


-- ================================  `EmptySet.interval_exact`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- For `0 < n`, as `Interval.empty_exact`: in dimension `0` a box with no coordinates contains the
one point. -/
theorem EmptySet.interval_exact (E : EmptySet n) (hn : 0 < n) :
    E.interval.construct = construct E :=
  Interval.empty_exact hn


-- =================================  `EmptySet.isBounded_iff`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `Bool` `EmptySet.isBounded` is `true` exactly when the set is bounded: exact. -/
theorem EmptySet.isBounded_iff (F : EmptySet n) :
    F.isBounded = true ↔ Bornology.IsBounded F.construct := by
  simp [EmptySet.isBounded, EmptySet.construct]


-- ===================================  `EmptySet.not_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `EmptySet.not` is the complement -/
theorem EmptySet.not_exact (E : EmptySet n) : E.not.construct = (E.construct)ᶜ := by
  change (Set.univ : Set (Vec ℝ n)) = (∅ : Set (Vec ℝ n))ᶜ
  exact Set.compl_empty.symm


-- =================================  `EmptySet.not_isFullDim`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- Its interior is `∅`, in every dimension. -/
theorem EmptySet.not_isFullDim (E : EmptySet n) : ¬ ContSet.IsFullDim E := by
  change ¬ (interior (∅ : Set (Vec ℝ n))).Nonempty
  rw [interior_empty]
  exact Set.not_nonempty_empty


-- ===================================  `EmptySet.volume_eq`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- `0`, CORA's value, is the volume of `∅`. -/
theorem EmptySet.volume_eq (E : EmptySet n) :
    MeasureTheory.volume (construct E) = E.volume := by
  change MeasureTheory.volume (∅ : Set (Vec ℝ n)) = 0
  exact MeasureTheory.measure_empty


-- ================================  `EmptySet.vPolytope_exact`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `EmptySet.vPolytope` denotes the empty set -/
theorem EmptySet.vPolytope_exact (E : EmptySet n) :
    E.vPolytope.construct = construct E :=
  VPolytope.construct_emptySet

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
