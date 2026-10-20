module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.DependentTerms
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.DependentTermsOuter
public import CORALean.ContSet.Interval.Real.Theorems.PowersOuter
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

@[expose] public section

/-!
# The powers from the exact square enclose the powers of every member

`expm` and `expmMixed` start `powers` at `intSq` of `dependentTerms(intMat * (1/r), r)`, which is
`r² (M/r)² = M²` for the member `M`; so the power of order `j ≥ 2`, `M ^ 2 * M ^ (j - 2)`, is in
`powers A intSq (j - 2)` (`powers_outer`).

## Inputs
* `A` – interval matrix
* `r` – step length
* `M` – member matrix
* `j` – power

## Hypotheses
* `hr` – step length nonzero
* `hM` – member lies in the interval matrix
* `hj` – power at least two

## Conclusion
* the member's power lies in the power enclosure from the exact square
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `M ^ j` is in the power of order `j` that starts from the exact square, for `j ≥ 2`. -/
theorem MatExp.powers_intSq_mem (A : Interval (Mat ℝ n n)) {r : ℝ} (hr : r ≠ 0)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) {j : ℕ} (hj : 2 ≤ j) : -- --- CONCL ---
    M ^ j ∈ (Interval.powers A
      (MatExp.dependentTerms (Interval.smul (1 / r) A) r).intSq
        (j - 2)).construct := by -- --- PROOF ---
  -- the member scaled by `1 / r` is in the scaled box, so its square is in `intSq`
  have hM' : r⁻¹ • M ∈ (Interval.smul (1 / r) A).construct := by
    have h := Interval.smul_outer (1 / r) A hM
    simpa only [one_div] using h
  have hsq := (MatExp.dependentTerms_outer (Interval.smul (1 / r) A) r hM').1
  have hMM : M * M = r ^ 2 • ((r⁻¹ • M) * (r⁻¹ • M)) := by
    rw [smul_mul_smul_comm, smul_smul]
    have : r ^ 2 * (r⁻¹ * r⁻¹) = 1 := by field_simp
    rw [this, one_smul]
  rw [← hMM] at hsq
  have h := Interval.powers_outer A _ hM hsq (j - 2)
  rwa [← pow_two, ← pow_add, show 2 + (j - 2) = j by omega] at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
