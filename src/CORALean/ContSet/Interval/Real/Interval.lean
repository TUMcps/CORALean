import CORALean.ContSet.ContSet.API

/-!
# Intervals: the representation

CORA's `interval`, with the same `inf` and `sup` fields, denoting the points
each coordinate's bounds admit.

Over any ambient type that has coordinates, so `Interval (Mat ℝ m n)` is CORA's
`intervalMatrix` and needs no separate representation. What a box means is
entrywise wherever it lives; only which index set it runs over changes.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Last revision: ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

structure Interval (α : Type) where
  inf : α
  sup : α

/-- `sup i < inf i` denotes the empty set `∅` -/
def Interval.construct (I : Interval α) : Set α :=
  {x | ∀ i, entry I.inf i ≤ entry x i ∧ entry x i ≤ entry I.sup i}

/-- checked in `Theorems.isNonempty_iff` -/
def Interval.IsNonempty (I : Interval α) : Prop := ∀ i : ι, entry I.inf i ≤ entry I.sup i

/-- Membership in an interval matrix, read with two indices rather than one
pair, which is the form every enclosure proof states its bounds in. -/
theorem Interval.mem_mat_iff {m n : ℕ} {I : Interval (Mat ℝ m n)} {A : Mat ℝ m n} :
    A ∈ I.construct ↔ ∀ i j, I.inf i j ≤ A i j ∧ A i j ≤ I.sup i j :=
  ⟨fun h i j => h (i, j), fun h p => h p.1 p.2⟩

/-- The midpoint, and half the width. Named because an enclosure proof splits a
box that way: a point it denotes is the centre off by at most the radius. -/
noncomputable def Interval.center (I : Interval α) : α := (2:ℝ)⁻¹ • (I.inf + I.sup)

noncomputable def Interval.radius (I : Interval α) : α := (2:ℝ)⁻¹ • (I.sup - I.inf)

theorem Interval.abs_sub_center_le {I : Interval α} {x : α} (hx : x ∈ I.construct) (i : ι) :
    |entry x i - entry I.center i| ≤ entry I.radius i := by
  have h := hx i
  rw [Interval.center, Interval.radius, entry_smul, entry_smul, entry_add, entry_sub, abs_le]
  constructor <;> linarith [h.1, h.2]

end CORALean.Real
