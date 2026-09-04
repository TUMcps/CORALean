import CORALean.ContSet.Interval.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import CORALean.ContSet.Interval.Real.Theorems.MtimesOuter

/-!
# `Interval.mtimesIntervalMat` over-approximates every matrix in the box

The whole content is one scalar fact: a product of two bounded factors is
bounded by the four corner products. It follows from `mul_between_endpoints`
twice — once holding the argument fixed and moving the coefficient, once the
other way — so no case split on signs appears here.

Outer and never exact for the same reason `Interval.mtimes` is not: the rows are
summed independently, so the result admits combinations of the corner extremes
that no single matrix in the box realises.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {m n : ℕ}

/-- A product of two bounded factors never leaves the hull of the four corner
products. -/
theorem Interval.aux_mul_between_corners {a b c d y x : ℝ} (hy₁ : a ≤ y) (hy₂ : y ≤ b)
    (hx₁ : c ≤ x) (hx₂ : x ≤ d) :
    Interval.mulLo a b c d ≤ y * x ∧ y * x ≤ Interval.mulHi a b c d := by
  have hy := Interval.mul_between_endpoints (c := x) hy₁ hy₂
  have ha := Interval.mul_between_endpoints (c := a) hx₁ hx₂
  have hb := Interval.mul_between_endpoints (c := b) hx₁ hx₂
  constructor
  · calc Interval.mulLo a b c d
        ≤ min (a * x) (b * x) := min_le_min ha.1 hb.1
      _ = min (x * a) (x * b) := by rw [mul_comm a x, mul_comm b x]
      _ ≤ x * y                := hy.1
      _ = y * x                := mul_comm x y
  · calc y * x = x * y := mul_comm y x
      _ ≤ max (x * a) (x * b) := hy.2
      _ = max (a * x) (b * x) := by rw [mul_comm x a, mul_comm x b]
      _ ≤ Interval.mulHi a b c d := max_le_max ha.2 hb.2

-- and a sum of such products lies between the two corner sums, term by term
theorem Interval.mtimesIntervalMat_outer (IM : Interval (Mat ℝ m n))
    (I : Interval (Vec ℝ n)) :
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' I.construct)
      ⊆ (Interval.mtimesIntervalMat IM I).construct := by
  rintro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, x, hx, rfl⟩ := hy
  intro i
  have hA' := Interval.mem_mat_iff.mp hA
  -- `entry` at a vector is the coordinate, definitionally
  have hx' : ∀ k, I.inf k ≤ x k ∧ x k ≤ I.sup k := fun k => hx k
  show (∑ k, Interval.mulLo (IM.inf i k) (IM.sup i k) (I.inf k) (I.sup k))
        ≤ ∑ k, A i k * x k
      ∧ (∑ k, A i k * x k)
        ≤ ∑ k, Interval.mulHi (IM.inf i k) (IM.sup i k) (I.inf k) (I.sup k)
  exact ⟨Finset.sum_le_sum fun k _ =>
           (Interval.aux_mul_between_corners (hA' i k).1 (hA' i k).2
             (hx' k).1 (hx' k).2).1,
         Finset.sum_le_sum fun k _ =>
           (Interval.aux_mul_between_corners (hA' i k).1 (hA' i k).2
             (hx' k).1 (hx' k).2).2⟩

end CORALean.Real
