import CORALean.ContDynamics.NonlinearSys.Definitions.AdmissibleLinError
import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# `L̂ ≤ L̄` does not keep the error set inside `[-θ r, θ r]`

[1, Eq. 7] asserts that `[-L̂, L̂] ⊆ M [-θ r, θ r]`, `M := (e^{Ar} - I)⁻¹ A`, "is
fulfilled if `|M| θ r =: L̄ ≥ L̂`", so that `R̄err(r) = A⁻¹(e^{Ar} - I)[-L̂, L̂]` stays
inside the box (6). `|M| θ r` is the radius of the *interval hull* of `M [-θ r, θ r]`,
and a box inside the hull of a parallelotope need not be inside the parallelotope.

At `A = [[1, 1], [0, 2]]`, `r = 1`, `θ = (1, 1)` and `L̂ = L̄`, the corner
`L̂` of `[-L̂, L̂]` is sent by `N := A⁻¹(e^{A} - I)` to a point whose first coordinate
is `(3e - 1)/(e + 1) > 1`. The arithmetic is exact: `A` is `V diag(1, 2) V⁻¹` with
`V = [[1, 1], [0, 1]]`, so `e^{A} = [[e, e² - e], [0, e²]]`, and both inverses are
upper triangular. Any `A` with two distinct real eigenvalues and non-orthogonal
eigenvectors does the same; in one dimension, or at a diagonal `A`, the claim holds.

A counterexample, and so real only: nothing is computed.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The counterexample's system matrix. -/
noncomputable def aux_A : Mat ℝ 2 2 := !![1, 1; 0, 2]

/-- `e^{A}` in closed form, through `A = V diag(1, 2) V⁻¹`. -/
theorem aux_exp_A :
    NormedSpace.exp ((1 : ℝ) • aux_A)
      = !![Real.exp 1, Real.exp 1 ^ 2 - Real.exp 1; 0, Real.exp 1 ^ 2] := by -- --- PROOF ---
  set V : Mat ℝ 2 2 := !![1, 1; 0, 1]
  have hVinv : V⁻¹ = !![1, -1; 0, 1] := by
    refine Matrix.inv_eq_left_inv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [V, Matrix.mul_apply, Fin.sum_univ_two]
  have hV : IsUnit V := by
    rw [Matrix.isUnit_iff_isUnit_det]; simp [V, Matrix.det_fin_two]
  have hA : (1 : ℝ) • aux_A = V * diagonal ![1, 2] * V⁻¹ := by
    rw [hVinv, one_smul, Matrix.diagonal_fin_two]
    simp only [V, aux_A, Matrix.mul_fin_two]
    norm_num
  rw [hA, Matrix.exp_conj _ _ hV, Matrix.exp_diagonal, hVinv, Pi.exp_def,
    Matrix.diagonal_fin_two]
  simp only [V, Matrix.mul_fin_two, ← Real.exp_eq_exp_ℝ]
  rw [show Real.exp 1 ^ 2 = Real.exp 2 by rw [← Real.exp_nat_mul]; norm_num]
  norm_num
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 7] is false as printed: at a `2 × 2` system, `L̂ = L̄` and `θ = (1, 1)`, the
set `A⁻¹(e^{Ar} - I)[-L̂, L̂]` leaves `[-θ r, θ r]`. -/
theorem NonlinearSys.admissibleLinError_not_sufficient :
    ∃ (A : Mat ℝ 2 2) (r : ℝ) (θ L : Vec ℝ 2),
      IsUnit A ∧ IsUnit (NormedSpace.exp (r • A) - 1) ∧ 0 < r ∧
      (∀ i, L i ≤ NonlinearSys.admissibleLinError A r θ i) ∧
      ¬ (fun x => (A⁻¹ * (NormedSpace.exp (r • A) - 1)) *ᵥ x) ''
          (⟨-L, L⟩ : Real.Interval (Vec ℝ 2)).construct
        ⊆ (⟨-(r • θ), r • θ⟩ : Real.Interval (Vec ℝ 2)).construct := by -- --- PROOF ---
  -- every entry is a rational function of `e`, which is all `field_simp` needs
  set e := Real.exp 1 with he
  have he2 : 2 < e := by have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have h1 : e - 1 ≠ 0 := by linarith
  have h2 : e ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : e + 1 ≠ 0 := by linarith
  have hE : NormedSpace.exp ((1 : ℝ) • aux_A) - 1 = !![e - 1, e ^ 2 - e; 0, e ^ 2 - 1] := by
    rw [aux_exp_A, Matrix.one_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [he]
  have hEinv : (!![e - 1, e ^ 2 - e; 0, e ^ 2 - 1] : Mat ℝ 2 2)⁻¹
      = !![1 / (e - 1), -e / (e ^ 2 - 1); 0, 1 / (e ^ 2 - 1)] := by
    refine Matrix.inv_eq_left_inv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (field_simp; try ring)
  have hAinv : aux_A⁻¹ = !![1, -1 / 2; 0, 1 / 2] := by
    refine Matrix.inv_eq_left_inv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [aux_A, Matrix.mul_apply, Fin.sum_univ_two]
  -- `L̄`, entry by entry: `|M| (1, 1)` with `M = [[1/(e-1), -1/(e+1)], [0, 2/(e²-1)]]`
  have hL : NonlinearSys.admissibleLinError aux_A 1 ![1, 1]
      = ![1 / (e - 1) + 1 / (e + 1), 2 / (e ^ 2 - 1)] := by
    simp only [NonlinearSys.admissibleLinError, hE, hEinv]
    ext i; fin_cases i <;>
      simp [Real.MatExp.absMat, aux_A, Matrix.mulVec, dotProduct, Matrix.mul_apply,
        Fin.sum_univ_two]
    · have key : (e - 1)⁻¹ + -e / (e ^ 2 - 1) * 2 = -(e + 1)⁻¹ := by
        have : e ^ 2 - 1 = (e - 1) * (e + 1) := by ring
        rw [this]; field_simp; ring
      rw [key, abs_neg, abs_of_pos (by linarith), abs_of_pos (inv_pos.mpr (by linarith))]
    · rw [abs_of_pos (by nlinarith)]; ring
  set L : Vec ℝ 2 := ![1 / (e - 1) + 1 / (e + 1), 2 / (e ^ 2 - 1)] with hLdef
  have hL0 : 0 ≤ L 0 := by
    simp only [hLdef, Matrix.cons_val_zero]
    exact add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg zero_le_one (by linarith))
  have hL1 : 0 ≤ L 1 := by
    simp only [hLdef, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact div_nonneg (by norm_num) (by nlinarith)
  -- `A` and `e^{A} - I` are triangular with nonzero diagonals, so both invertible
  refine ⟨aux_A, 1, ![1, 1], L, ?_, ?_, one_pos, fun i => by rw [hL], ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det]; simp [aux_A, Matrix.det_fin_two]
  · rw [hE, Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
    simp only [mul_zero, sub_zero, isUnit_iff_ne_zero]; exact mul_ne_zero h1 h2
  · intro hsub
    have hmem : L ∈ (⟨-L, L⟩ : Real.Interval (Vec ℝ 2)).construct := by
      intro i
      change -L i ≤ L i ∧ L i ≤ L i
      refine ⟨?_, le_rfl⟩
      fin_cases i
      · exact neg_le_self hL0
      · exact neg_le_self hL1
    have h0 : ((aux_A⁻¹ * (NormedSpace.exp ((1 : ℝ) • aux_A) - 1)) *ᵥ L) 0
        ≤ ((1 : ℝ) • (![1, 1] : Vec ℝ 2)) 0 := (hsub ⟨L, hmem, rfl⟩ 0).2
    rw [hAinv, hE] at h0
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, hLdef] at h0
    -- the corner lands at `(3e - 1)/(e + 1)`, which is past `1` since `e > 1`
    have key : (e - 1) * ((e - 1)⁻¹ + (e + 1)⁻¹) + (e ^ 2 - e + -1 / 2 * (e ^ 2 - 1))
        * (2 / (e ^ 2 - 1)) = (3 * e - 1) / (e + 1) := by
      have : e ^ 2 - 1 = (e - 1) * (e + 1) := by ring
      rw [this]; field_simp; ring
    rw [key, div_le_one (by linarith)] at h0
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
