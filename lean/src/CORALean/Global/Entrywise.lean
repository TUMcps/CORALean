import CORALean.Global.Tensor

/-!
# Ambient types that have coordinates

An axis-aligned box, a generator ranking and an entrywise radius bound all read
a point coordinate by coordinate. This says which ambient types allow that, and
what an index is: `Fin n` for a vector, `Fin m × Fin n` for a matrix.

`entry` is required linear and injective, which is what lets an operation be
defined entrywise and still be the operation on the space — `Interval.plus`
adds bounds, and the sum of what two boxes denote is what the summed box
denotes only because reading entries commutes with addition.

Not a `LinearEquiv`: nothing here needs to build a point *from* coordinates, and
requiring surjectivity would exclude an ambient type whose coordinates are
constrained.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

class Entrywise (α : Type) (ι : outParam Type) [AddCommGroup α] [Module ℝ α] where
  entry : α → ι → ℝ
  /-- The point with the given coordinates. `linComb` needs it: the bounds it
  produces are a `min` and a `max` read off two others. -/
  ofEntry : (ι → ℝ) → α
  entry_ofEntry (f : ι → ℝ) (i : ι) : entry (ofEntry f) i = f i
  ofEntry_entry (a : α) : ofEntry (entry a) = a
  entry_add (a b : α) (i : ι) : entry (a + b) i = entry a i + entry b i
  entry_smul (c : ℝ) (a : α) (i : ι) : entry (c • a) i = c * entry a i

namespace Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

attribute [simp] entry_ofEntry

theorem entry_injective : Function.Injective (entry : α → ι → ℝ) := by
  intro a b h
  rw [← ofEntry_entry a, ← ofEntry_entry b, h]

@[simp] theorem entry_zero (i : ι) : entry (0 : α) i = 0 := by
  have h := entry_add (0 : α) 0 i
  rw [add_zero] at h
  linarith

@[simp] theorem entry_neg (a : α) (i : ι) : entry (-a) i = -entry a i := by
  have h := entry_add a (-a) i
  rw [add_neg_cancel, entry_zero] at h
  linarith

theorem entry_sub (a b : α) (i : ι) : entry (a - b) i = entry a i - entry b i := by
  rw [sub_eq_add_neg, entry_add, entry_neg, sub_eq_add_neg]

/-- Two points with the same coordinates are the same point. -/
theorem ext {a b : α} (h : ∀ i, entry a i = entry b i) : a = b :=
  entry_injective (funext h)

end Entrywise

/-- A vector is its own coordinates. -/
instance {n : ℕ} : Entrywise (Vec ℝ n) (Fin n) where
  entry v i := v i
  ofEntry f := f
  entry_ofEntry _ _ := rfl
  ofEntry_entry _ := rfl
  entry_add _ _ _ := rfl
  entry_smul _ _ _ := rfl

/-- True by `rfl`, but a proof stated in coordinates has to rewrite with it. -/
@[simp] theorem Entrywise.entry_vec {n : ℕ} (v : Vec ℝ n) (i : Fin n) :
    Entrywise.entry v i = v i := rfl

/-- A matrix is indexed by a pair. Its own type former, not `Tensor`, so this
instance does not collide with the vector one. -/
instance {m n : ℕ} : Entrywise (Mat ℝ m n) (Fin m × Fin n) where
  entry A p := A p.1 p.2
  ofEntry f := fun i j => f (i, j)
  entry_ofEntry _ _ := rfl
  ofEntry_entry _ := rfl
  entry_add _ _ _ := rfl
  entry_smul _ _ _ := rfl

@[simp] theorem Entrywise.entry_mat {m n : ℕ} (A : Mat ℝ m n) (p : Fin m × Fin n) :
    Entrywise.entry A p = A p.1 p.2 := rfl

end CORALean
