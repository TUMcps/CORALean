import CORALean.ContSet.Interval.Real.Definitions.Hull
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The interval hull of a box under a nonnegative matrix

[1, Lemma 5], corrected: for `I = [a, b]` and `A ≥ 0` elementwise, `Box(A I) = [A a, A b]`. Each
coordinate of `A x` is monotone in `x`, so it is least at `a` and greatest at `b`, both in `I`.
The lemma also prints `A I = [A a, A b]`, the image itself a box, which is false
(`image_of_nonneg_counterexample`); only the hull is.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.hull_image_of_nonneg (A : Mat ℝ m n) (hA : ∀ i j, 0 ≤ A i j) (a b : Vec ℝ n)
    (hab : ∀ j, a j ≤ b j) :
    Interval.hull ((A *ᵥ ·) '' (⟨a, b⟩ : Interval (Vec ℝ n)).construct) =
      ⟨A *ᵥ a, A *ᵥ b⟩ := by -- --- PROOF ---
  have ha : a ∈ (⟨a, b⟩ : Interval (Vec ℝ n)).construct := fun j => ⟨le_rfl, hab j⟩
  have hb : b ∈ (⟨a, b⟩ : Interval (Vec ℝ n)).construct := fun j => ⟨hab j, le_rfl⟩
  -- a coordinate of `A x` is monotone in `x`
  have hmono : ∀ x y : Vec ℝ n, (∀ j, x j ≤ y j) → ∀ i, (A *ᵥ x) i ≤ (A *ᵥ y) i :=
    fun x y h i => by
      simp only [mulVec, dotProduct]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hA i j)
  simp only [Interval.hull, Set.image_image]
  congr 1 <;> funext i
  · refine IsLeast.csInf_eq ⟨⟨a, ha, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hmono a x (fun j => (hx j).1) i
  · refine IsGreatest.csSup_eq ⟨⟨b, hb, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hmono x b (fun j => (hx j).2) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
