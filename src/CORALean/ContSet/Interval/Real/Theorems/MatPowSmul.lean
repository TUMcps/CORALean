module

public import CORALean.ContSet.Interval.Real.Operations.MatPow
public import CORALean.ContSet.Interval.Real.Operations.Smul

@[expose] public section

/-!
# `Interval.matPow` of a non-negatively scaled box

At `s ≥ 0`, the `k`-th power of the box `s • A` has `s ^ k` times the endpoints
of `A`'s own `k`-th power — endpoint for endpoint, not only up to enclosure.
Every corner product of `matMul` scales by the product of the two factors'
scales, and `smul`'s `min`/`max` reorder the endpoints only in a way the
corner products cannot see.

It is what lets a bound proved once against the unscaled box, at every time `s`
of a step, be read off the box of the step `smul s A` itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The least corner product scales by both factors' non-negative scales. -/
theorem aux_mulLo_scale {a b c d x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Interval.mulLo (x * a) (x * b) (y * c) (y * d) = x * y * Interval.mulLo a b c d := by
  have e : ∀ p q : ℝ, x * p * (y * q) = x * y * (p * q) := fun p q => by ring
  simp only [Interval.mulLo, e, mul_min_of_nonneg _ _ (mul_nonneg hx hy)]

/-- The greatest likewise. -/
theorem aux_mulHi_scale {a b c d x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Interval.mulHi (x * a) (x * b) (y * c) (y * d) = x * y * Interval.mulHi a b c d := by
  have e : ∀ p q : ℝ, x * p * (y * q) = x * y * (p * q) := fun p q => by ring
  simp only [Interval.mulHi, e, mul_max_of_nonneg _ _ (mul_nonneg hx hy)]

/-- Ordering the first pair changes no corner product's value. -/
theorem aux_mulLo_minmax (a b c d : ℝ) :
    Interval.mulLo (min a b) (max a b) c d = Interval.mulLo a b c d := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]; simp only [Interval.mulLo]; exact min_comm _ _

/-- The greatest likewise. -/
theorem aux_mulHi_minmax (a b c d : ℝ) :
    Interval.mulHi (min a b) (max a b) c d = Interval.mulHi a b c d := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]; simp only [Interval.mulHi]; exact max_comm _ _


-- =======================================  MAIN THEOREM  ======================================= --

/-- The power of a non-negatively scaled box is the power of the box, its
endpoints scaled by `s ^ k`. -/
theorem Interval.matPow_smul (A : Interval (Mat ℝ n n)) {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    (Interval.matPow (Interval.smul s A) k).inf = s ^ k • (Interval.matPow A k).inf ∧
    (Interval.matPow (Interval.smul s A) k).sup
      = s ^ k • (Interval.matPow A k).sup := by -- --- PROOF ---
  induction k with
  | zero => simp [Interval.matPow, Interval.point]
  | succ k ih =>
    constructor
    · funext i j
      show ∑ l, Interval.mulLo _ _ ((Interval.matPow (Interval.smul s A) k).inf l j)
          ((Interval.matPow (Interval.smul s A) k).sup l j) = s ^ (k + 1) *
          ∑ l, Interval.mulLo (A.inf i l) (A.sup i l) _ _
      rw [ih.1, ih.2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Interval.smul, Entrywise.ofEntry, Entrywise.entry, Matrix.smul_apply,
        smul_eq_mul]
      -- `smul`'s endpoints are the scaled ones, possibly swapped, which `mulLo` ignores
      rw [← mul_min_of_nonneg _ _ hs, ← mul_max_of_nonneg _ _ hs,
        aux_mulLo_scale hs (pow_nonneg hs k), aux_mulLo_minmax, pow_succ']
    · funext i j
      show ∑ l, Interval.mulHi _ _ ((Interval.matPow (Interval.smul s A) k).inf l j)
          ((Interval.matPow (Interval.smul s A) k).sup l j) = s ^ (k + 1) *
          ∑ l, Interval.mulHi (A.inf i l) (A.sup i l) _ _
      rw [ih.1, ih.2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Interval.smul, Entrywise.ofEntry, Entrywise.entry, Matrix.smul_apply,
        smul_eq_mul]
      rw [← mul_min_of_nonneg _ _ hs, ← mul_max_of_nonneg _ _ hs,
        aux_mulHi_scale hs (pow_nonneg hs k), aux_mulHi_minmax, pow_succ']

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
