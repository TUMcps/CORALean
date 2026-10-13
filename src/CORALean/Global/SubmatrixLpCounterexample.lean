module

public import CORALean.Global.SubmatrixLp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-!
# The printed (13) is infeasible and the printed (16) unsound

[1, Eq. 13] asks `xₖₗ ⟨aₖₗ⟩ > ∑ᵢ ∑ⱼ xᵢⱼ (1 - xᵢₗ) |aᵢₗ|` for every `k, l`: at an `xₖₗ = 0` the left
side is `0` and the right a sum of non-negative terms, so no `x` with a zero entry is
feasible, and with two or more columns the row constraint forces one
(`subLp13_infeasible`). (14) is the intended implication `xₖₗ = 1 → …`, and
`det_submatrix_ne_zero_of_lp14` proves it sound.

[1, Eq. 16] is (15) with `+μ` for `-μ`: at `xₖₗ = 1` it allows the column sum to reach
`⟨aₖₗ⟩ + μ`, no longer strict. For the all-ones `2 × 2` matrix, `x = I`, `μ = 1/100` and the
paper's `M = ∑ aᵢⱼ = 4`, every constraint of (16) holds and the picked matrix is singular
(`subLp16_counterexample`).

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Finset

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 13] has no binary solution with at most one pick per row once `m ≥ 2`. -/
theorem subLp13_infeasible (hn : 0 < n) (hm : 2 ≤ m) {mig mag : Matrix (Fin n) (Fin m) ℝ}
    (hmag : ∀ i j, 0 ≤ mag i j) (x : Matrix (Fin n) (Fin m) ℝ) (hbin : ∀ i j, x i j = 0 ∨ x i j = 1)
    (hrow : ∀ i, ∑ j, x i j ≤ 1) :
    ¬ ∀ k l, x k l * mig k l > ∑ i, ∑ j, x i j * (1 - x i l) * mag i l := by -- --- PROOF ---
  intro h13
  let i₀ : Fin n := ⟨0, hn⟩
  -- two picks in row `i₀` would sum to `2`, so some `x i₀ l` is `0`
  obtain ⟨l, hl⟩ : ∃ l, x i₀ l = 0 := by
    by_contra hne
    simp only [not_exists] at hne
    have h1 : ∀ j, x i₀ j = 1 := fun j => (hbin i₀ j).resolve_left (hne j)
    have := hrow i₀
    simp only [h1, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have h := h13 i₀ l
  rw [hl, zero_mul] at h
  have hnn : 0 ≤ ∑ i, ∑ j, x i j * (1 - x i l) * mag i l := sum_nonneg fun i _ =>
    sum_nonneg fun j _ => by
      rcases hbin i j with h0 | h0 <;> rcases hbin i l with h1 | h1 <;>
        simp [h0, h1, hmag i l]
  linarith

/-- [1, Eq. 16]: all its constraints hold for the singular all-ones matrix at `x = I`. -/
theorem subLp16_counterexample :
    let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => 1
    let x : Matrix (Fin 2) (Fin 2) ℝ := 1
    let μ : ℝ := 1 / 100
    let M : ℝ := ∑ i, ∑ j, A i j
    0 < μ ∧ (∀ k l, ∑ i ∈ univ.erase k, ∑ j, x i j * |A i l| ≤ M + (|A k l| + μ - M) * x k l) ∧
      (A.submatrix id id).det = 0 := by
  intro A x μ M
  refine ⟨by norm_num [μ], fun k l => ?_, by simp [A, det_fin_two]⟩
  fin_cases k <;> fin_cases l <;>
    simp [A, x, μ, M, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
