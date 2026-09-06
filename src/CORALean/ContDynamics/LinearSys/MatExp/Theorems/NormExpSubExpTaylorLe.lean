import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.FactorialMulPowLe

/-!
# The matrix exponential's Taylor truncation error, bounded

[1, Eq. (3.2)–(3.3)]. The tail past `η` is dominated term by term by a
geometric series of ratio `‖x‖ / (η + 2)`, because `(η+1+i)!` outgrows
`(η+1)!` by at least `(η+2)` a step. Summing that geometric series is where the
`1 / (1 - ε)` comes from, and where `ε < 1` is needed.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The same estimate at a matrix, reached through the norm of its powers. -/
theorem aux_term_le (x : Mat ℝ n n) (η i : ℕ) :
    ‖((Nat.factorial (i + (η + 1)) : ℝ)⁻¹) • x ^ (i + (η + 1))‖
      ≤ (‖x‖ ^ (η + 1) / Nat.factorial (η + 1)) * (‖x‖ / ((η : ℝ) + 2)) ^ i := by -- --- PROOF ---
  rw [Nat.add_comm i (η + 1)]
  have hfac : ((Nat.factorial (η + 1) : ℝ) * ((η : ℝ) + 2) ^ i)
      ≤ (Nat.factorial ((η + 1) + i) : ℝ) := by
    have hcast : ((Nat.factorial (η + 1) * ((η + 1) + 1) ^ i : ℕ) : ℝ)
        ≤ ((Nat.factorial ((η + 1) + i) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (factorial_mul_pow_le (η + 1) i)
    push_cast at hcast
    convert hcast using 3
    ring
  rw [norm_smul, norm_inv, Real.norm_natCast]
  have hnp : ‖x ^ ((η + 1) + i)‖ ≤ ‖x‖ ^ ((η + 1) + i) := norm_pow_le' x (by omega)
  calc (Nat.factorial ((η + 1) + i) : ℝ)⁻¹ * ‖x ^ ((η + 1) + i)‖
      ≤ (Nat.factorial ((η + 1) + i) : ℝ)⁻¹ * ‖x‖ ^ ((η + 1) + i) := by gcongr
    _ ≤ ((Nat.factorial (η + 1) : ℝ) * ((η : ℝ) + 2) ^ i)⁻¹ * ‖x‖ ^ ((η + 1) + i) := by gcongr
    _ = (‖x‖ ^ (η + 1) / Nat.factorial (η + 1)) * (‖x‖ / ((η : ℝ) + 2)) ^ i := by
        rw [div_pow, pow_add]
        field_simp


-- =======================================  MAIN THEOREM  ======================================= --

-- summability and `tsum` over the matrix algebra is the cost here, not the estimate
set_option maxHeartbeats 1000000 in
theorem norm_exp_sub_expTaylor_le (x : Mat ℝ n n) (η : ℕ)
    (hε : ‖x‖ / ((η : ℝ) + 2) < 1) :
    ‖exp x - MatExp.expTaylor x η‖ ≤ MatExp.expRemainderBound x η := by -- --- PROOF ---
  show ‖exp x - ∑ i ∈ Finset.range (η + 1), ((Nat.factorial i : ℝ)⁻¹) • x ^ i‖
      ≤ (‖x‖ ^ (η + 1) / Nat.factorial (η + 1)) * (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹
  set f : ℕ → Mat ℝ n n := fun i => ((Nat.factorial i : ℝ)⁻¹) • x ^ i with hf
  have hsum : Summable f := expSeries_summable' (𝕂 := ℝ) x
  have hnorm : Summable (fun i => ‖f i‖) := norm_expSeries_summable' (𝕂 := ℝ) x
  have hε0 : (0:ℝ) ≤ ‖x‖ / ((η : ℝ) + 2) := by positivity
  have hgeo : Summable (fun i : ℕ => (‖x‖ / ((η : ℝ) + 2)) ^ i) :=
    summable_geometric_of_lt_one hε0 hε
  have hx : exp x = ∑' i : ℕ, f i := by rw [exp_eq_tsum (𝕂 := ℝ)]
  have htail : exp x - ∑ i ∈ Finset.range (η + 1), f i = ∑' i : ℕ, f (i + (η + 1)) := by
    rw [hx, ← hsum.sum_add_tsum_nat_add (η + 1)]
    abel
  rw [htail]
  -- norm of the tail sum under the sum of norms, then the geometric closed form
  calc ‖∑' i : ℕ, f (i + (η + 1))‖
      ≤ ∑' i : ℕ, ‖f (i + (η + 1))‖ :=
        norm_tsum_le_tsum_norm ((summable_nat_add_iff (η + 1)).mpr hnorm)
    _ ≤ ∑' i : ℕ, (‖x‖ ^ (η + 1) / Nat.factorial (η + 1)) * (‖x‖ / ((η : ℝ) + 2)) ^ i :=
        Summable.tsum_le_tsum (fun i => aux_term_le x η i)
          ((summable_nat_add_iff (η + 1)).mpr hnorm) (hgeo.mul_left _)
    _ = (‖x‖ ^ (η + 1) / Nat.factorial (η + 1)) * (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hε0 hε]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
