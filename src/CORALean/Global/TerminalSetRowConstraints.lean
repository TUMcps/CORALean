import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Diagonal

/-!
# The row constraints of the terminal set program

[1, Eq. 55], [1, Eq. 56] and [1, Eq. 57]: for scalings `sⱼ > 0` and `Z'` with rows `ζⱼ`, the
`L⊤₁,q` norm of `Diag(s)⁻¹ Z'`, the `q`-norm of the vector of its rows' absolute sums, is at most
one iff `‖ζⱼ‖₁ ≤ sⱼ` for every `j` at `q = ∞` (Eq. 55), iff `Σⱼ ‖ζⱼ‖₁² / sⱼ² ≤ 1` at `q = 2`
(Eq. 56); and `‖ζⱼ‖₁ ≤ sⱼ / √m` for every `j`, the linear constraint that replaces the convex one,
implies Eq. 56 (Eq. 57).

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The rows' absolute sums of `Diag(s)⁻¹ Z'`: `Σᵢ |Z'ⱼᵢ| / sⱼ`. -/
theorem aux_rowSum_diagonal_inv_mul (s : Fin m → ℝ) (hs : ∀ j, 0 < s j)
    (Z' : Matrix (Fin m) (Fin n) ℝ) (j : Fin m) :
    ∑ i, |(Matrix.diagonal (fun j => (s j)⁻¹) * Z') j i| = (∑ i, |Z' j i|) / s j := by
  simp only [Matrix.diagonal_mul, abs_mul, abs_inv, abs_of_pos (hs j), ← Finset.mul_sum]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem rowSumNorm_infty_le_one_iff (s : Fin m → ℝ) (hs : ∀ j, 0 < s j)
    (Z' : Matrix (Fin m) (Fin n) ℝ) :
    ‖WithLp.toLp ∞ (fun j => ∑ i, |(Matrix.diagonal (fun j => (s j)⁻¹) * Z') j i|)‖ ≤ 1 ↔
      ∀ j, ∑ i, |Z' j i| ≤ s j := by -- --- PROOF ---
  simp only [aux_rowSum_diagonal_inv_mul s hs Z', PiLp.norm_eq_ciSup, Real.norm_eq_abs]
  have hnn : ∀ j, 0 ≤ (∑ i, |Z' j i|) / s j := fun j =>
    div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (hs j).le
  constructor
  · -- each entry is below the supremum, which is at most one
    intro h j
    have := (le_ciSup (f := fun j => |(∑ i, |Z' j i|) / s j|)
      (Set.finite_range _).bddAbove j).trans h
    rwa [abs_of_nonneg (hnn j), div_le_one (hs j)] at this
  · intro h
    refine Real.iSup_le (fun j => ?_) zero_le_one
    rw [abs_of_nonneg (hnn j), div_le_one (hs j)]
    exact h j

theorem rowSumNorm_two_le_one_iff (s : Fin m → ℝ) (hs : ∀ j, 0 < s j)
    (Z' : Matrix (Fin m) (Fin n) ℝ) :
    ‖WithLp.toLp 2 (fun j => ∑ i, |(Matrix.diagonal (fun j => (s j)⁻¹) * Z') j i|)‖ ≤ 1 ↔
      ∑ j, (∑ i, |Z' j i|) ^ 2 / s j ^ 2 ≤ 1 := by -- --- PROOF ---
  -- the squared Euclidean norm is the sum of the squared entries
  have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin m => ℝ)
    (WithLp.toLp 2 (fun j => ∑ i, |(Matrix.diagonal (fun j => (s j)⁻¹) * Z') j i|))
  simp only [aux_rowSum_diagonal_inv_mul s hs Z', Real.norm_eq_abs, sq_abs] at hsq
  have hterm : ∀ j, ((∑ i, |Z' j i|) / s j) ^ 2 = (∑ i, |Z' j i|) ^ 2 / s j ^ 2 :=
    fun j => div_pow _ _ _
  simp only [hterm] at hsq
  simp only [aux_rowSum_diagonal_inv_mul s hs Z']
  rw [← sq_le_one_iff₀ (norm_nonneg _), hsq]

theorem rowSumNorm_two_le_one_of_le (s : Fin m → ℝ) (hs : ∀ j, 0 < s j)
    (Z' : Matrix (Fin m) (Fin n) ℝ) (h : ∀ j, ∑ i, |Z' j i| ≤ s j / Real.sqrt m) :
    ∑ j, (∑ i, |Z' j i|) ^ 2 / s j ^ 2 ≤ 1 := by -- --- PROOF ---
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  -- each term is at most `1 / m`, and there are `m` of them
  have hterm : ∀ j, (∑ i, |Z' j i|) ^ 2 / s j ^ 2 ≤ 1 / m := by
    intro j
    have hnn : 0 ≤ ∑ i, |Z' j i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [div_le_div_iff₀ (pow_pos (hs j) 2) hmpos, one_mul]
    have h1 := h j
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hmpos)] at h1
    have := mul_self_le_mul_self (mul_nonneg hnn (Real.sqrt_nonneg _)) h1
    rw [mul_mul_mul_comm, Real.mul_self_sqrt hmpos.le] at this
    nlinarith
  calc _ ≤ ∑ _j : Fin m, (1 : ℝ) / m := Finset.sum_le_sum fun j _ => hterm j
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
