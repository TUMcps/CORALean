module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.EmptySet.Real.EmptySet
public import CORALean.ContSet.Fullspace.Real.Fullspace
public import CORALean.ContSet.Fullspace.Real.Operations.And
public import CORALean.ContSet.Fullspace.Real.Operations.Basic
public import CORALean.ContSet.Fullspace.Real.Operations.Box
public import CORALean.ContSet.Fullspace.Real.Operations.Center
public import CORALean.ContSet.Fullspace.Real.Operations.EnclosePoints
public import CORALean.ContSet.Fullspace.Real.Operations.HPolytope
public import CORALean.ContSet.Fullspace.Real.Operations.Isequal
public import CORALean.ContSet.Fullspace.Real.Operations.Not
public import CORALean.ContSet.Fullspace.Real.Theorems.DisjointIff
public import CORALean.ContSet.Fullspace.Real.Theorems.IsBoundedConstructIff
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# `ContSet/Fullspace/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- ==================================  `Fullspace.and_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Intersecting the full space with a set of any representation gives that set. -/
theorem Fullspace.and_exact {S : Type} [ContSet S (Vec ℝ n)] (F : Fullspace n) (s : S) :
    ContSet.construct (F.and_ s) = F.construct ∩ ContSet.construct s := by
  change ContSet.construct s = Set.univ ∩ ContSet.construct s
  exact (Set.univ_inter _).symm


-- ==================================  `Fullspace.box_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The box of the full space denotes the full space. -/
theorem Fullspace.box_exact (F : Fullspace n) : F.box.construct = F.construct := rfl


-- =============================  `Fullspace.center_mem_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Trivially, as it contains everything. -/
theorem Fullspace.center_mem_construct (F : Fullspace n) : F.center ∈ F.construct :=
  Set.mem_univ _


-- ================================  `Fullspace.construct_Inf`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Fullspace.Inf` denotes everything -/
theorem Fullspace.construct_Inf : (Fullspace.Inf n).construct = (Set.univ : Set (Vec ℝ n)) := rfl


-- ================================  `Fullspace.convHull_exact`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Exact for any operand: the hull contains the whole space already. -/
theorem Fullspace.convHull_exact {S : Type} [ContSet S (Vec ℝ n)] (F : Fullspace n) (s : S) :
    convexHull ℝ (F.construct ∪ ContSet.construct s) = (F.convHull s).construct :=
  Set.eq_univ_of_univ_subset ((Set.subset_union_left).trans (subset_convexHull ℝ _))


-- ===============================  `Fullspace.hPolytope_exact`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- `Fullspace.hPolytope` denotes the full space -/
theorem Fullspace.hPolytope_exact (F : Fullspace n) :
    F.hPolytope.construct = F.construct :=
  HPolytope.construct_fullspace


-- ================================  `Fullspace.isBounded_iff`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `Bool` `Fullspace.isBounded` is `true` exactly when the set is bounded: exact. -/
theorem Fullspace.isBounded_iff (F : Fullspace n) :
    F.isBounded = true ↔ Bornology.IsBounded F.construct := by
  simpa [Fullspace.isBounded] using (Fullspace.isBounded_construct_iff F).symm


-- =================================  `Fullspace.isequal_iff`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Both denote the whole space, so `true` is the right answer, and it is the answer exactly when
the sets are equal. -/
theorem Fullspace.isequal_iff (E F : Fullspace n) :
    E.isequal F = true ↔ E.construct = F.construct :=
  ⟨fun _ => rfl, fun _ => rfl⟩


-- ===============================  `Fullspace.not_disjoint_iff`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The full space meets a set iff it is nonempty -/
theorem Fullspace.not_disjoint_iff {S : Type} [ContSet S (Vec ℝ n)] (F : Fullspace n) (s : S) :
    ¬Disjoint (ContSet.construct s) F.construct ↔ (ContSet.construct s).Nonempty := by
  rw [Fullspace.disjoint_iff, Set.nonempty_iff_ne_empty]


-- ==================================  `Fullspace.not_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Fullspace.not` is the complement -/
theorem Fullspace.not_exact (F : Fullspace n) : F.not.construct = (F.construct)ᶜ := by
  change (∅ : Set (Vec ℝ n)) = (Set.univ : Set (Vec ℝ n))ᶜ
  exact Set.compl_univ.symm


-- ==========================  `Fullspace.range_subset_enclosePoints`  ========================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Fullspace.enclosePoints` encloses the points -/
theorem Fullspace.range_subset_enclosePoints {p : ℕ} (pts : Fin p → Vec ℝ n) :
    Set.range pts ⊆ (Fullspace.enclosePoints pts).construct :=
  fun _ _ => Set.mem_univ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
