import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrCoeffLeOne
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SumExpTail2Le

/-!
# How wide the correction matrix is, in `r` and `‖A‖` alone

Both endpoints at once, since an error measure has to bound whatever the
interval denotes and not only one side of it. Each order contributes at most
`(r‖A‖)^i / i!` — the coefficient is in `[-1, 0]` and an entry of `A^i` never
exceeds `‖A‖^i` — so the finite part is under `e^{r‖A‖} - 1 - r‖A‖`, and the
tail is the same `expRemainderBound` the enclosure was built with.

Indexed from `2`, which is where the interpolation error starts, so the whole
bound is `O(r²)`: the correction is second order in the step where the hull it
corrects is only first order.

The side condition is what makes `expRemainderBound` nonnegative; without it the
geometric factor is negative and the two endpoints are crossed.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One order of the interpolation error, in `r` and `‖A‖`. -/
theorem MatExp.aux_abs_corrTerm_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 ≤ r) (i : ℕ) (j k : Fin n) :
    |MatExp.corrTerm A r (i + 2) j k|
      ≤ (Nat.factorial (i + 2) : ℝ)⁻¹ * (r * ‖A‖) ^ (i + 2) := by -- --- PROOF ---
  have hfac : (0:ℝ) < (Nat.factorial (i + 2) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (i + 2)
  have hcc : |MatExp.corrCoeff (i + 2)| ≤ 1 := MatExp.abs_corrCoeff_le_one (by omega)
  have hentry : |(A ^ (i + 2)) j k| ≤ ‖A‖ ^ (i + 2) :=
    (abs_entry_le_norm _ j k).trans (norm_pow_le' A (by omega))
  have hexp : |MatExp.corrTerm A r (i + 2) j k| = |MatExp.corrCoeff (i + 2)| * r ^ (i + 2)
      * ((Nat.factorial (i + 2) : ℝ)⁻¹ * |(A ^ (i + 2)) j k|) := by
    rw [MatExp.corrTerm, abs_mul, abs_mul, abs_mul, abs_inv,
      abs_of_nonneg (pow_nonneg hr _), abs_of_nonneg hfac.le]
  rw [hexp, mul_pow]
  have hstep : |MatExp.corrCoeff (i + 2)| * r ^ (i + 2)
        * ((Nat.factorial (i + 2) : ℝ)⁻¹ * |(A ^ (i + 2)) j k|)
      ≤ 1 * r ^ (i + 2) * ((Nat.factorial (i + 2) : ℝ)⁻¹ * ‖A‖ ^ (i + 2)) := by
    have h0 : (0:ℝ) ≤ r ^ (i + 2) := pow_nonneg hr _
    gcongr
  refine hstep.trans (le_of_eq ?_)
  ring

/-- Clamping at zero never grows a value in absolute terms, either way round. -/
theorem aux_abs_clamp_le (t : ℝ) : |min t 0| ≤ |t| ∧ |max t 0| ≤ |t| := by -- --- PROOF ---
  rcases le_total t 0 with ht | ht
  · rw [min_eq_left ht, max_eq_right ht]
    exact ⟨le_refl _, by rw [abs_zero]; exact abs_nonneg t⟩
  · rw [min_eq_right ht, max_eq_left ht]
    exact ⟨by rw [abs_zero]; exact abs_nonneg t, le_refl _⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Neither endpoint of the correction matrix leaves the ball the step and the
order name. -/
theorem MatExp.abs_correctionMatrix_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 ≤ r) {η : ℕ}
    (hε : ‖r • A‖ / ((η : ℝ) + 2) < 1) (j k : Fin n) :
    |(MatExp.correctionMatrix A r η).inf j k|
        ≤ Real.exp (r * ‖A‖) - 1 - r * ‖A‖ + MatExp.expRemainderBound (r • A) η
      ∧ |(MatExp.correctionMatrix A r η).sup j k|
        ≤ Real.exp (r * ‖A‖) - 1 - r * ‖A‖
          + MatExp.expRemainderBound (r • A) η := by -- --- PROOF ---
  have hc : (0:ℝ) ≤ r * ‖A‖ := mul_nonneg hr (norm_nonneg _)
  have hb0 : (0:ℝ) ≤ MatExp.expRemainderBound (r • A) η := by
    rw [MatExp.expRemainderBound]
    have h1 : (0:ℝ) < 1 - ‖r • A‖ / ((η : ℝ) + 2) := by linarith
    positivity
  -- the finite part, whichever way its orders are clamped
  have hpart : ∀ g : ℝ → ℝ, (∀ t, |g t| ≤ |t|) →
      |∑ i ∈ Finset.range (η - 1), g (MatExp.corrTerm A r (i + 2) j k)|
        ≤ Real.exp (r * ‖A‖) - 1 - r * ‖A‖ := by
    intro g hg
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun i _ =>
      (hg _).trans (MatExp.aux_abs_corrTerm_le A hr i j k)) ?_
    exact sum_expTail2_le hc (η - 1)
  -- the two endpoints clamp the same orders in opposite directions
  have hmin := hpart (fun t => min t 0) fun t => (aux_abs_clamp_le t).1
  have hmax := hpart (fun t => max t 0) fun t => (aux_abs_clamp_le t).2
  constructor
  · show |(∑ i ∈ Finset.range (η - 1), min (MatExp.corrTerm A r (i + 2) j k) 0)
      - MatExp.expRemainderBound (r • A) η| ≤ _
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hb0]
    linarith
  · show |(∑ i ∈ Finset.range (η - 1), max (MatExp.corrTerm A r (i + 2) j k) 0)
      + MatExp.expRemainderBound (r • A) η| ≤ _
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hb0]
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
