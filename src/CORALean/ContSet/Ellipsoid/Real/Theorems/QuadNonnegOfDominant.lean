import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# A symmetric diagonally dominant matrix has a nonnegative quadratic form

Gershgorin for the quadratic form: if every diagonal entry is at least the sum of the absolute
off-diagonal entries of its row, `vᵀ M v ≥ 0`. Each off-diagonal term is bounded
`M_ij v_i v_j ≥ -|M_ij| (v_i² + v_j²)/2`, and by symmetry the sums of the two squares agree, so
what remains is `Σ_i v_i² (M_ii - Σ_{j≠i} |M_ij|)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.quad_nonneg_of_dominant {n : ℕ} (M : Mat ℝ n n) (hsymm : ∀ i j, M i j = M j i)
    (hdom : ∀ i, ∑ j, (if i = j then 0 else |M i j|) ≤ M i i) (v : Vec ℝ n) :
    0 ≤ v ⬝ᵥ (M *ᵥ v) := by -- --- PROOF ---
  -- `W i j` is the absolute off-diagonal entry, zero on the diagonal
  set W : Fin n → Fin n → ℝ := fun i j => if i = j then 0 else |M i j| with hW
  have hWsymm : ∀ i j, W i j = W j i := fun i j => by
    simp only [hW, hsymm i j]
    by_cases h : i = j <;> simp [h, eq_comm]
  -- each term of the form is at least its diagonal part less the shared squares
  have hterm : ∀ i j, (if i = j then M i i * v i ^ 2 else 0) - W i j * (v i ^ 2 + v j ^ 2) / 2
      ≤ v i * (M i j * v j) := fun i j => by
    by_cases h : i = j
    · subst h; simp [hW]; nlinarith
    · simp only [h, if_false, hW]
      have h1 : |M i j * (v i * v j)| ≤ |M i j| * ((v i ^ 2 + v j ^ 2) / 2) := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        nlinarith [sq_nonneg (|v i| - |v j|), abs_mul_abs_self (v i), abs_mul_abs_self (v j),
          abs_mul (v i) (v j), abs_nonneg (v i), abs_nonneg (v j)]
      have h2 := (abs_le.mp h1).1
      nlinarith
  have hsum : ∑ i, ∑ j, ((if i = j then M i i * v i ^ 2 else 0) - W i j * (v i ^ 2 + v j ^ 2) / 2)
      ≤ ∑ i, ∑ j, v i * (M i j * v j) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  -- the two squares contribute the same sum, by symmetry of `W`
  have hswap : ∑ i, ∑ j, W i j * v j ^ 2 / 2 = ∑ i, ∑ j, W i j * v i ^ 2 / 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hWsymm i j]
  -- the diagonal terms and the row sums, as one expression
  have hdiag : ∑ i, ∑ j, (if i = j then M i i * v i ^ 2 else 0) = ∑ i, M i i * v i ^ 2 := by
    simp
  have hrow : ∑ i, ∑ j, W i j * v i ^ 2 / 2 = ∑ i, (∑ j, W i j) * v i ^ 2 / 2 :=
    Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_div, ← Finset.sum_mul]
  have hform : ∑ i, ∑ j, ((if i = j then M i i * v i ^ 2 else 0) - W i j * (v i ^ 2 + v j ^ 2) / 2)
      = ∑ i, M i i * v i ^ 2 - ∑ i, (∑ j, W i j) * v i ^ 2 := by
    have : ∀ i j, ((if i = j then M i i * v i ^ 2 else 0) - W i j * (v i ^ 2 + v j ^ 2) / 2)
        = (if i = j then M i i * v i ^ 2 else 0) - W i j * v i ^ 2 / 2 - W i j * v j ^ 2 / 2 :=
      fun i j => by ring
    simp only [this, Finset.sum_sub_distrib]
    linarith [hswap, hdiag, hrow, Finset.sum_div Finset.univ (fun i => (∑ j, W i j) * v i ^ 2) 2]
  -- what remains is `Σ v_i² (M_ii - row sum)`, nonnegative by dominance
  have hnn : 0 ≤ ∑ i, M i i * v i ^ 2 - ∑ i, (∑ j, W i j) * v i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _ => by nlinarith [sq_nonneg (v i), hdom i]
  have : v ⬝ᵥ (M *ᵥ v) = ∑ i, ∑ j, v i * (M i j * v j) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [this]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
