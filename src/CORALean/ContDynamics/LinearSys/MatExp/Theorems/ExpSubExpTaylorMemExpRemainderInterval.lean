import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsPowEntryLeAbsMatPow
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HasSumExpRemainderMatEntry
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul

/-!
# The Taylor remainder of `e^{At}` lies in `[-W(t), W(t)]`

[1, Eq. 6]: `e^{At} ∈ Σᵢ₌₀^η (At)ⁱ/i! ⊕ Ê(t)`, `Ê(t) = [-W(t), W(t)]` with
`W(t) = |Σᵢ>η Aⁱtⁱ/i!| ≤ Σᵢ>η |A|ⁱtⁱ/i! = e^{|A|t} - Σᵢ₌₀^η |A|ⁱtⁱ/i!`, entrywise, for `t ≥ 0`.
The right-hand side is `expRemainderMat`, and the chain is the printed one: each entry of the
remainder is the series' tail, its terms bounded by those of the `|A|` series,
`abs_pow_entry_le_absMat_pow_entry`, whose tail is `hasSum_expRemainderMat_entry`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- `exp_smul_tsum` and the shifted `tsum` re-solve the four local normed-algebra instances
set_option maxHeartbeats 400000 in
/-- [1, Eq. 6]: `e^{At} - Σᵢ₌₀^η (At)ⁱ/i! ∈ [-W(t), W(t)]` at `t ≥ 0`. -/
theorem MatExp.exp_sub_expTaylor_mem_expRemainderInterval (A : Mat ℝ n n) {t : ℝ} (ht : 0 ≤ t)
    (η : ℕ) :
    exp (t • A) - MatExp.expTaylor (t • A) η
      ∈ MatExp.expRemainderInterval A t η := by -- --- PROOF ---
  intro j k
  set h : ℕ → Mat ℝ n n := fun i => ((Nat.factorial i : ℝ)⁻¹ * t ^ i) • A ^ i with hh
  have hsum : Summable h := summable_exp_smul A t
  have htay : MatExp.expTaylor (t • A) η = ∑ i ∈ Finset.range (η + 1), h i :=
    Finset.sum_congr rfl fun i _ => by rw [hh]; simp only; rw [smul_pow, smul_smul]
  -- the remainder is the series' tail, entry by entry
  have hE : exp (t • A) - MatExp.expTaylor (t • A) η = ∑' i, h (i + (η + 1)) := by
    rw [exp_smul_tsum A t, htay, ← hsum.sum_add_tsum_nat_add (η + 1)]
    abel
  have htail := ((summable_nat_add_iff (η + 1)).mpr hsum).hasSum
  rw [← hE] at htail
  have ha := Pi.hasSum.mp (Pi.hasSum.mp htail j) k
  have hb := MatExp.hasSum_expRemainderMat_entry A t η j k
  -- each term within the `|A|` series' term
  have hle : ∀ i, |h (i + (η + 1)) j k| ≤ ((Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * t ^ (i + (η + 1)))
      * ((MatExp.absMat A) ^ (i + (η + 1))) j k := fun i => by
    simp only [hh, Matrix.smul_apply, smul_eq_mul]
    rw [abs_mul, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * t ^ (i + (η + 1)))]
    exact mul_le_mul_of_nonneg_left (abs_pow_entry_le_absMat_pow_entry A _ j k) (by positivity)
  exact abs_le.mpr ⟨by
      have := hasSum_le (fun i => (abs_le.mp (hle i)).1) hb.neg ha
      linarith,
    hasSum_le (fun i => (abs_le.mp (hle i)).2) ha hb⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
