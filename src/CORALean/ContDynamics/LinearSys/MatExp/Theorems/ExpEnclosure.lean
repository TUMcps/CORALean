import CORALean.ContDynamics.LinearSys.MatExp.Enclosures

/-!
# The matrix exponential lies in its enclosure

Althoff's thesis (2010), Eq. (3.2)–(3.3). The tail past `η` is dominated term by
term by a geometric series of ratio `‖x‖ / (η + 2)`, because `(η+1+i)!` outgrows
`(η+1)!` by at least `(η+2)` a step. Summing that geometric series is where the
`1 / (1 - ε)` comes from, and where `ε < 1` is needed.

The bound is on the operator norm and the enclosure is entrywise, which is sound
because under the `l∞` operator norm an entry never exceeds its row sum, and a
row sum never exceeds the norm.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-- Under the `l∞` operator norm an entry never exceeds the whole norm. -/
theorem abs_entry_le_norm {m k : ℕ} (M : Mat ℝ m k) (i : Fin m) (j : Fin k) :
    |M i j| ≤ ‖M‖ := by
  have h : ‖M i j‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact le_trans (Finset.single_le_sum (f := fun j => ‖M i j‖₊)
      (fun _ _ => zero_le) (Finset.mem_univ j))
      (Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ i))
  rw [← Real.norm_eq_abs]
  exact_mod_cast h

/-- `(a+k)!` outgrows `a` factorial by at least `(a+1)` each step, which is what
makes the tail geometric. -/
theorem aux_factorial_mul_pow_le (a k : ℕ) :
    Nat.factorial a * (a + 1) ^ k ≤ Nat.factorial (a + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : Nat.factorial (a + (k + 1)) = (a + k + 1) * Nat.factorial (a + k) := by
      rw [← Nat.add_assoc]; exact Nat.factorial_succ _
    calc Nat.factorial a * (a + 1) ^ (k + 1)
        = (Nat.factorial a * (a + 1) ^ k) * (a + 1) := by ring
      _ ≤ Nat.factorial (a + k) * (a + 1)           := Nat.mul_le_mul_right _ ih
      _ ≤ Nat.factorial (a + k) * (a + k + 1)       := Nat.mul_le_mul_left _ (by omega)
      _ = Nat.factorial (a + (k + 1))               := by rw [hstep]; ring

/-- The scalar core of the tail estimate: the factorial outgrows the power fast
enough that the tail is dominated by a geometric series. Stated on its own
because the correction matrix bounds a different series with the same shape. -/
theorem aux_scalar_term_le {c : ℝ} (hc : 0 ≤ c) (η i : ℕ) :
    (Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * c ^ (i + (η + 1))
      ≤ (c ^ (η + 1) / Nat.factorial (η + 1)) * (c / ((η : ℝ) + 2)) ^ i := by
  rw [Nat.add_comm i (η + 1)]
  have hfac : ((Nat.factorial (η + 1) : ℝ) * ((η : ℝ) + 2) ^ i)
      ≤ (Nat.factorial ((η + 1) + i) : ℝ) := by
    have hcast : ((Nat.factorial (η + 1) * ((η + 1) + 1) ^ i : ℕ) : ℝ)
        ≤ ((Nat.factorial ((η + 1) + i) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (aux_factorial_mul_pow_le (η + 1) i)
    push_cast at hcast
    convert hcast using 3
    ring
  calc (Nat.factorial ((η + 1) + i) : ℝ)⁻¹ * c ^ ((η + 1) + i)
      ≤ ((Nat.factorial (η + 1) : ℝ) * ((η : ℝ) + 2) ^ i)⁻¹ * c ^ ((η + 1) + i) := by gcongr
    _ = (c ^ (η + 1) / Nat.factorial (η + 1)) * (c / ((η : ℝ) + 2)) ^ i := by
        rw [div_pow, pow_add]
        field_simp

theorem aux_term_le (x : Mat ℝ n n) (η i : ℕ) :
    ‖((Nat.factorial (i + (η + 1)) : ℝ)⁻¹) • x ^ (i + (η + 1))‖
      ≤ (‖x‖ ^ (η + 1) / Nat.factorial (η + 1)) * (‖x‖ / ((η : ℝ) + 2)) ^ i := by
  rw [Nat.add_comm i (η + 1)]
  have hfac : ((Nat.factorial (η + 1) : ℝ) * ((η : ℝ) + 2) ^ i)
      ≤ (Nat.factorial ((η + 1) + i) : ℝ) := by
    have hcast : ((Nat.factorial (η + 1) * ((η + 1) + 1) ^ i : ℕ) : ℝ)
        ≤ ((Nat.factorial ((η + 1) + i) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (aux_factorial_mul_pow_le (η + 1) i)
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

-- Summability and tsum over a matrix algebra is what costs here, not the
-- estimate: every step re-finds the normed-algebra instance on `Mat`.
set_option maxHeartbeats 1000000 in
theorem norm_exp_sub_expTaylor_le (x : Mat ℝ n n) (η : ℕ)
    (hε : ‖x‖ / ((η : ℝ) + 2) < 1) :
    ‖exp x - MatExp.expTaylor x η‖ ≤ MatExp.expRemainderBound x η := by
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
  calc ‖∑' i : ℕ, f (i + (η + 1))‖
      ≤ ∑' i : ℕ, ‖f (i + (η + 1))‖ :=
        norm_tsum_le_tsum_norm ((summable_nat_add_iff (η + 1)).mpr hnorm)
    _ ≤ ∑' i : ℕ, (‖x‖ ^ (η + 1) / Nat.factorial (η + 1)) * (‖x‖ / ((η : ℝ) + 2)) ^ i :=
        Summable.tsum_le_tsum (fun i => aux_term_le x η i)
          ((summable_nat_add_iff (η + 1)).mpr hnorm) (hgeo.mul_left _)
    _ = (‖x‖ ^ (η + 1) / Nat.factorial (η + 1)) * (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hε0 hε]

/-- Monotone in the norm of its argument, which is what lets one bound taken at
the end of a step stand for every time inside it. -/
theorem MatExp.expRemainderBound_mono {x y : Mat ℝ n n} (η : ℕ) (hxy : ‖x‖ ≤ ‖y‖)
    (hy : ‖y‖ / ((η : ℝ) + 2) < 1) :
    MatExp.expRemainderBound x η ≤ MatExp.expRemainderBound y η := by
  have h2 : (0:ℝ) < (η : ℝ) + 2 := by positivity
  have hfrac : ‖x‖ / ((η : ℝ) + 2) ≤ ‖y‖ / ((η : ℝ) + 2) := by gcongr
  have hdy : 0 < 1 - ‖y‖ / ((η : ℝ) + 2) := by linarith
  have hdx : 0 < 1 - ‖x‖ / ((η : ℝ) + 2) := by linarith
  have hnum : ‖x‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)
      ≤ ‖y‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := by gcongr
  have hinv : (1 - ‖x‖ / ((η : ℝ) + 2))⁻¹ ≤ (1 - ‖y‖ / ((η : ℝ) + 2))⁻¹ :=
    inv_anti₀ hdy (by linarith)
  exact mul_le_mul hnum hinv (inv_nonneg.mpr hdx.le) (by positivity)

theorem MatExp.exp_mem_expEnclosure (x : Mat ℝ n n) (η : ℕ)
    (hε : ‖x‖ / ((η : ℝ) + 2) < 1) :
    exp x ∈ (MatExp.expEnclosure x η).construct := by
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have h : |exp x i j - MatExp.expTaylor x η i j|
      ≤ MatExp.expRemainderBound x η := by
    calc |exp x i j - MatExp.expTaylor x η i j|
        = |(exp x - MatExp.expTaylor x η) i j| := by rw [Matrix.sub_apply]
      _ ≤ ‖exp x - MatExp.expTaylor x η‖ := abs_entry_le_norm _ i j
      _ ≤ MatExp.expRemainderBound x η := norm_exp_sub_expTaylor_le x η hε
  rw [abs_le] at h
  constructor
  · show MatExp.expTaylor x η i j - MatExp.expRemainderBound x η ≤ exp x i j
    linarith [h.1]
  · show exp x i j ≤ MatExp.expTaylor x η i j + MatExp.expRemainderBound x η
    linarith [h.2]

end CORALean.Real
