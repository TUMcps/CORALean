module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrCoeffLeOne
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SumExpTailLe

@[expose] public section

/-!
# How wide the integrated correction matrix is, in `r` and `‖A‖` alone

`AbsCorrectionMatrixLe` for `constCorrectionMatrix`, which is [1]'s `G(Δt,η)`
of eq. (16) — the same orders one factorial further along and one matrix power
back, which is what integrating each order of the exponential does to it.

Every order carries an extra `r` over `correctionMatrix`'s, so the whole bound
is `r·(e^{r‖A‖} - 1)` against that file's `e^{r‖A‖} - 1 - r‖A‖`: one power of
the step cheaper in the factorial, one power of the step dearer in front. The
`(i+2)!` is discarded down to `(i+1)!` so that `sum_expTail_le` applies; nothing
sharper is needed, the use being an asymptotic bound in `r`.

The side condition is what makes `expRemainderBound` nonnegative; without it the
geometric factor is negative and the two endpoints are crossed.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Inner- and Outer-Approximations of
      Reachable Sets". IEEE Transactions on Automatic Control, vol. 68, no. 12,
      2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One order of the integrated interpolation error, in `r` and `‖A‖`. -/
theorem MatExp.aux_abs_constCorrTerm_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 ≤ r) (i : ℕ)
    (j k : Fin n) : |MatExp.constCorrTerm A r i j k|
      ≤ r * ((Nat.factorial (i + 1) : ℝ)⁻¹ * (r * ‖A‖) ^ (i + 1)) := by -- --- PROOF ---
  have hfac2 : (0:ℝ) < (Nat.factorial (i + 2) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (i + 2)
  have hcc : |MatExp.corrCoeff (i + 2)| ≤ 1 := MatExp.abs_corrCoeff_le_one (by omega)
  have hentry : |(A ^ (i + 1)) j k| ≤ ‖A‖ ^ (i + 1) :=
    (abs_entry_le_norm _ j k).trans (norm_pow_le' A (by omega))
  have hexp : |MatExp.constCorrTerm A r i j k| = |MatExp.corrCoeff (i + 2)| * r ^ (i + 2)
      * ((Nat.factorial (i + 2) : ℝ)⁻¹ * |(A ^ (i + 1)) j k|) := by
    rw [MatExp.constCorrTerm, abs_mul, abs_mul, abs_mul, abs_inv,
      abs_of_nonneg (pow_nonneg hr _), abs_of_nonneg hfac2.le]
  -- clamp the coefficient and the entry, then trade `(i+2)!` down to `(i+1)!`
  have hstep : |MatExp.corrCoeff (i + 2)| * r ^ (i + 2)
        * ((Nat.factorial (i + 2) : ℝ)⁻¹ * |(A ^ (i + 1)) j k|)
      ≤ 1 * r ^ (i + 2) * ((Nat.factorial (i + 1) : ℝ)⁻¹ * ‖A‖ ^ (i + 1)) := by
    have hfacle : (Nat.factorial (i + 2) : ℝ)⁻¹ ≤ (Nat.factorial (i + 1) : ℝ)⁻¹ := by
      have h : (Nat.factorial (i + 1) : ℝ) ≤ (Nat.factorial (i + 2) : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega)
      exact inv_anti₀ (by exact_mod_cast Nat.factorial_pos (i + 1)) h
    have h0 : (0:ℝ) ≤ r ^ (i + 2) := pow_nonneg hr _
    gcongr
  rw [hexp]
  refine hstep.trans (le_of_eq ?_)
  rw [mul_pow]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- Neither endpoint of the integrated correction matrix leaves the ball the
step and the order name. -/
theorem MatExp.abs_constCorrectionMatrix_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 ≤ r) {η : ℕ}
    (hε : ‖r • A‖ / ((η : ℝ) + 2) < 1) (j k : Fin n) :
    |(MatExp.constCorrectionMatrix A r η).inf j k|
        ≤ r * (Real.exp (r * ‖A‖) - 1) + r * MatExp.expRemainderBound (r • A) η
      ∧ |(MatExp.constCorrectionMatrix A r η).sup j k|
        ≤ r * (Real.exp (r * ‖A‖) - 1)
          + r * MatExp.expRemainderBound (r • A) η := by -- --- PROOF ---
  have hc : (0:ℝ) ≤ r * ‖A‖ := mul_nonneg hr (norm_nonneg _)
  have hb0 : (0:ℝ) ≤ r * MatExp.expRemainderBound (r • A) η := by
    rw [MatExp.expRemainderBound]
    have h1 : (0:ℝ) < 1 - ‖r • A‖ / ((η : ℝ) + 2) := by linarith
    positivity
  -- clamping at zero never grows a value in absolute terms, either way round
  have hclamp : ∀ t : ℝ, |min t 0| ≤ |t| ∧ |max t 0| ≤ |t| := by
    intro t
    rcases le_total t 0 with ht | ht
    · rw [min_eq_left ht, max_eq_right ht]
      exact ⟨le_refl _, by rw [abs_zero]; exact abs_nonneg t⟩
    · rw [min_eq_right ht, max_eq_left ht]
      exact ⟨by rw [abs_zero]; exact abs_nonneg t, le_refl _⟩
  -- the finite part, whichever way its orders are clamped
  have hpart : ∀ g : ℝ → ℝ, (∀ t, |g t| ≤ |t|) →
      |∑ i ∈ Finset.range η, g (MatExp.constCorrTerm A r i j k)|
        ≤ r * (Real.exp (r * ‖A‖) - 1) := by
    intro g hg
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun i _ =>
      (hg _).trans (MatExp.aux_abs_constCorrTerm_le A hr i j k)) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_expTail_le hc η) hr
  -- the two endpoints clamp the same orders in opposite directions
  have hmin := hpart (fun t => min t 0) fun t => (hclamp t).1
  have hmax := hpart (fun t => max t 0) fun t => (hclamp t).2
  constructor
  · show |(∑ i ∈ Finset.range η, min (MatExp.constCorrTerm A r i j k) 0)
      - r * MatExp.expRemainderBound (r • A) η| ≤ _
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hb0]
    linarith
  · show |(∑ i ∈ Finset.range η, max (MatExp.constCorrTerm A r i j k) 0)
      + r * MatExp.expRemainderBound (r • A) η| ≤ _
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hb0]
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
