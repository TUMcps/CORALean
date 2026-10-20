import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosure

/-!
# Enclosing the exponential of a whole box of matrices, not one member

`hε` is stated at `A.absMax`, not at any particular member: it has to be
checkable from the interval matrix alone, before a member is ever in hand, and
`A.absMax` is exactly the one fixed matrix `matPow` can be bounded against
independently of which member of `A` a given power came from.

The enclosure is not exact even here, where `A` holds only diagonal matrices:
`matPow A k` already admits different diagonal members at different powers `k`,
the ordinary interval-arithmetic dependency loss that compounds with `η`.

## Inputs
* none

## Output
* example interval matrix
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A diagonal box, `±0.01` on each entry: small enough that `hε` costs nothing
to check. -/
noncomputable def EIM.A : Interval (Mat ℝ 2 2) :=
  ⟨Matrix.diagonal ![(-0.01:ℝ), -0.01], Matrix.diagonal ![(0.01:ℝ), 0.01]⟩

/-- `A.absMax` is the same diagonal matrix at `0.01`: the two endpoints agree in
absolute value on the diagonal, and off it both endpoints are already `0`. -/
theorem EIM.absMax_eq : -- --- CONCL ---
    EIM.A.absMax = Matrix.diagonal (fun _ : Fin 2 => (0.01:ℝ)) := by -- --- PROOF ---
  funext i j
  rcases eq_or_ne i j with h | h
  · subst h
    fin_cases i <;> norm_num [Interval.absMax, EIM.A, Matrix.diagonal_apply_eq]
  · simp [Interval.absMax, EIM.A, Matrix.diagonal_apply_ne _ h]

/-- The dominating matrix's norm is exactly `0.01`, read off through
`linfty_opNorm_diagonal` rather than through the row-sum definition. -/
theorem EIM.norm_absMax_le : ‖EIM.A.absMax‖ ≤ (0.01:ℝ) := by
  rw [EIM.absMax_eq, Matrix.linfty_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun _ => by rw [Real.norm_eq_abs]; norm_num

/-- Checkable from `A` alone, before any member `M ∈ construct A` is in hand. -/
theorem EIM.hε : ‖EIM.A.absMax‖ / ((0:ℕ) + 2 : ℝ) < 1 := by
  have h := EIM.norm_absMax_le
  rw [Nat.cast_zero, zero_add]
  linarith

/-- The zero matrix is a member of `A`, and its exponential — the identity —
lands inside the enclosure `expIntervalEnclosure A 0` computes for it. -/
example : exp (0 : Mat ℝ 2 2) ∈ (MatExp.expIntervalEnclosure EIM.A 0).construct :=
  MatExp.exp_mem_expIntervalEnclosure EIM.A 0
    (show (0 : Mat ℝ 2 2) ∈ EIM.A.construct by
      rintro ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> norm_num [Interval.construct, EIM.A])
    EIM.hε

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
