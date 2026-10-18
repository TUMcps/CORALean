module

public import CORALean.Global.Tensor
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# A diagonally dominant symmetric matrix is positive semidefinite

The certificate a float test can check for `⪰ 0`: every diagonal entry at least the sum of the
magnitudes off the diagonal in its row. Each cross term `xᵢ Mᵢⱼ xⱼ` is at least
`-|Mᵢⱼ| (xᵢ² + xⱼ²) / 2`, and symmetry gives every row its own half of each, so the quadratic
form is at least `Σᵢ (Mᵢᵢ - Σⱼ≠ᵢ |Mᵢⱼ|) xᵢ² ≥ 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One cross term, at least its share of the off-diagonal penalty. -/
theorem SpectraShadow.aux_cross_term (M : Mat ℝ k k) (x : Fin k → ℝ) (i j : Fin k) : -- --- STMT ---
    (if j = i then M i i * x i ^ 2 else 0)
        - (if j = i then 0 else |M i j|) * x i ^ 2 / 2
        - (if j = i then 0 else |M i j|) * x j ^ 2 / 2
      ≤ x i * (M i j * x j) := by -- --- PROOF ---
  by_cases h : j = i
  · subst h
    simp only [if_true, zero_mul, zero_div, sub_zero]
    nlinarith
  · simp only [h, if_false, zero_sub]
    have hxy : |x i * x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    have hm : |M i j| * |x i * x j| ≤ |M i j| * ((x i ^ 2 + x j ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
    have hneg := neg_abs_le (M i j * (x i * x j))
    rw [abs_mul] at hneg
    nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.posSemidef_of_diagDominant (M : Mat ℝ k k) (hsym : ∀ i j, M j i = M i j)
    (hdom : ∀ i, ∑ j, (if j = i then 0 else |M i j|) ≤ M i i) :
    M.PosSemidef := by -- --- PROOF ---
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.IsHermitian.ext fun i j => by simp [hsym]) fun x => ?_
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
  set o : Fin k → Fin k → ℝ := fun i j => if j = i then 0 else |M i j| with ho
  set a : Fin k → Fin k → ℝ := fun i j => if j = i then M i i * x i ^ 2 else 0 with ha
  -- the off-diagonal penalty is symmetric, so the two halves charge the same total
  have hswap : ∑ i, ∑ j, o i j * x j ^ 2 / 2 = ∑ i, ∑ j, o i j * x i ^ 2 / 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [ho, hsym, eq_comm]
  have hhalf : ∑ i, ∑ j, (a i j - o i j * x i ^ 2 / 2 - o i j * x j ^ 2 / 2)
      = ∑ i, ∑ j, (a i j - o i j * x i ^ 2) := by
    have e : ∀ i j, a i j - o i j * x i ^ 2 / 2 - o i j * x j ^ 2 / 2
        = (a i j - o i j * x i ^ 2) + (o i j * x i ^ 2 / 2 - o i j * x j ^ 2 / 2) :=
      fun i j => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, hswap, sub_self, add_zero]
  -- each row's diagonal entry pays for its off-diagonal penalty
  have hrow : ∀ i, ∑ j, (a i j - o i j * x i ^ 2) = (M i i - ∑ j, o i j) * x i ^ 2 := by
    intro i
    rw [Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
    simp only [ha, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc (0 : ℝ) ≤ ∑ i, (M i i - ∑ j, o i j) * x i ^ 2 :=
        Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr (hdom i)) (sq_nonneg _)
    _ = ∑ i, ∑ j, (a i j - o i j * x i ^ 2 / 2 - o i j * x j ^ 2 / 2) := by
        rw [hhalf]
        exact Finset.sum_congr rfl fun i _ => (hrow i).symm
    _ ≤ ∑ i, ∑ j, x i * (M i j * x j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          SpectraShadow.aux_cross_term M x i j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
