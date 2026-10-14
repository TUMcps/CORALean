module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.EBoxConstruct
public import CORALean.ContSet.Interval.Real.Operations.Inf
public import CORALean.ContSet.Interval.Real.Operations.IsNonempty
public import CORALean.ContSet.Interval.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.Interval.Real.Operations.SupportBound
public import CORALean.ContSet.Interval.Real.Operations.Times
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Theorems.IsNonempty
public import CORALean.ContSet.Interval.Real.Theorems.LeSubset
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Real.Theorems.OrOuter
public import CORALean.ContSet.Interval.Real.Theorems.SupportBoundEntrywiseAttained
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Real.Sign
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `ContSet/Interval/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ============================  `Interval.construct_eq_of_isequal`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- Equal bounds give equal sets, with no hypothesis: containment each way. -/
theorem Interval.construct_eq_of_isequal {I J : Interval α} (h : I.isequal J) :
    I.construct = J.construct :=
  Set.Subset.antisymm (Interval.le_subset h.1) (Interval.le_subset h.2)

end CORALean.Real


-- ================================  `Interval.convHull_outer`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- A box is convex, so it contains the convex hull of whatever the union of two boxes lies in. -/
theorem Interval.convHull_outer (I₁ I₂ : Interval α) :
    convexHull ℝ (I₁.construct ∪ I₂.construct) ⊆ (I₁.convHull I₂).construct :=
  convexHull_min (Interval.or_outer I₁ I₂) (Interval.convex_construct _)

end CORALean.Real


-- ===================================  `Interval.Inf_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- The box `(-∞, ∞)ⁿ` denotes every point of `ℝⁿ`. -/
theorem Interval.Inf_exact (n : ℕ) : (Interval.Inf n).construct = Set.univ := by
  ext x
  simp [Interval.Inf, Interval.EBox.construct]

end CORALean.Real


-- =============================  `Interval.infimum_mem_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- Nonempty only: for crossed bounds the set is `∅`. -/
theorem Interval.infimum_mem_construct (I : Interval α) (h : I.IsNonempty) :
    I.infimum ∈ I.construct := fun i => ⟨le_rfl, h i⟩

end CORALean.Real


-- ==============================  `Interval.not_isNonempty_iff`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       17-August-2026
-- Last update:   04-September-2026
-- Reviewed:      ---

namespace CORALean.Real

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- The negation of `isNonempty_iff`, stated because that is the direction the
degenerate case is used in: an interval whose lower bound exceeds its upper one
is not a small box but no box at all. -/
theorem Interval.not_isNonempty_iff (I : Interval α) : ¬I.IsNonempty ↔ I.construct = ∅ := by
  rw [Interval.isNonempty_iff, Set.not_nonempty_iff_eq_empty]

end CORALean.Real


-- =================================  `Interval.project_outer`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n m : ℕ}

/-- Reading the same coordinates of a member. No hypothesis, and repeated coordinates are fine. -/
theorem Interval.project_outer (I : Interval (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' I.construct ⊆ (I.project dims).construct := by
  rintro _ ⟨x, hx, rfl⟩ k
  exact hx (dims k)

end CORALean.Real


-- ===========================  `Interval.representsa_emptySet_iff`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- Crossed bounds are exactly the empty set, `not_isNonempty_iff`. -/
theorem Interval.representsa_emptySet_iff (I : Interval α) :
    I.representsa_emptySet ↔ I.construct = ∅ :=
  Interval.not_isNonempty_iff I

end CORALean.Real


-- =============================  `Interval.supportBound_attained`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- `Interval.supportBoundEntrywise_attained` at the ambient type `Vec ℝ n`. -/
theorem Interval.supportBound_attained {n : ℕ} (I : Interval (Vec ℝ n))
    (c : Vec ℝ n →ₗ[ℝ] ℝ) (hI : I.IsNonempty) :
    ∃ x ∈ I.construct, c x = (I.supportBound c).val :=
  Interval.supportBoundEntrywise_attained I c hI

end CORALean.Real


-- ============================  `Interval.supremum_mem_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- Nonempty only: for crossed bounds the set is `∅`. -/
theorem Interval.supremum_mem_construct (I : Interval α) (h : I.IsNonempty) :
    I.supremum ∈ I.construct := fun i => ⟨h i, le_rfl⟩

end CORALean.Real


-- ==================================  `Interval.times_outer`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- Each coordinate is `mul_between_corners`. No hypothesis: it is an inclusion. -/
theorem Interval.times_outer (I J : Interval (Vec ℝ n)) :
    Set.image2 (fun x y i => x i * y i) I.construct J.construct ⊆ (I.times J).construct := by
  rintro _ ⟨x, hx, y, hy, rfl⟩ i
  exact Interval.mul_between_corners (hx i).1 (hx i).2 (hy i).1 (hy i).2

end CORALean.Real


-- ==================================  `Interval.uplus_exact`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- The set is unchanged, definitionally. -/
theorem Interval.uplus_exact (I : Interval α) : I.uplus.construct = I.construct := rfl

end CORALean.Real


-- =====================================  `sign_monotone`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- The sign function is a monotone step function. -/
theorem sign_monotone : Monotone Real.sign := by
  intro a b hab
  unfold Real.sign
  split_ifs <;> first | (exfalso; linarith) | norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
