import CORALean.ContDynamics.LinearSys.Operations.InputSolutionInner
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionSet
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpIntegralSubTaylorLe
import CORALean.ContSet.Interval.Real.Theorems.MemMat

/-!
# A step of the outer approximation is within `O(Δt²)` of the inner one

The outer half of [1, Prop. 1] needs an *upper* bound on its outer
approximation, which the sandwich alone cannot give. Every point of it is
`∑ᵢ AⁱΔt^{i+1}/(i+1)! sᵢ ⊕ M s'`, and measuring it against `expIntegral Δt s₀`
cancels the whole zeroth order `Δt s₀`: what is left is the orders `i ≥ 1`, the
remainder factor, and the series' own tail, each of them `O(Δt²)`.

`Δt‖A‖ ≤ 1` is what makes the geometric factor in `expRemainderBound` at most
`2` and `‖Δt·A‖^{η+1}` at most `‖Δt·A‖`, uniformly in the truncation order.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of a finite Minkowski sum of images names one point per summand. -/
theorem LinearSys.aux_exists_of_mem_sum (sys : LinearSys 𝕋 n) {U : S n} (Δt : ℝ)
    (hne : (construct U).Nonempty) (m : ℕ) :
    ∀ x ∈ ∑ i ∈ Finset.range m, (fun v => sys.inputTerm Δt i *ᵥ v) '' construct U,
      ∃ s : ℕ → Vec ℝ n, (∀ i, s i ∈ construct U) ∧
        x = ∑ i ∈ Finset.range m, sys.inputTerm Δt i *ᵥ s i := by -- --- PROOF ---
  obtain ⟨v₀, hv₀⟩ := hne
  induction m with
  | zero =>
    intro x hx
    refine ⟨fun _ => v₀, fun _ => hv₀, ?_⟩
    simpa using hx
  | succ k ih =>
    intro x hx
    rw [Finset.sum_range_succ] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hb
    obtain ⟨s', hs', rfl⟩ := ih a ha
    have hmem : ∀ i, (if i = k then w else s' i) ∈ construct U := by
      intro i; by_cases h : i = k <;> simp [h, hw, hs']
    refine ⟨fun i => if i = k then w else s' i, hmem, ?_⟩
    rw [Finset.sum_range_succ]
    congr 1
    · exact Finset.sum_congr rfl fun i hi => by
        simp only [if_neg (Finset.mem_range.mp hi).ne]
    · simp

/-- Every entry bounded gives a bound on the image, `n` entries per row. -/
theorem aux_norm_mulVec_le {M : Mat ℝ n n} {w : Vec ℝ n} {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ)
    (hM : ∀ j k, |M j k| ≤ c) (hw : ‖w‖ ≤ ρ) : ‖M *ᵥ w‖ ≤ (n : ℝ) * c * ρ := by -- --- PROOF ---
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  rw [Real.norm_eq_abs]
  calc |(M *ᵥ w) j| = |∑ k, M j k * w k| := by rw [Matrix.mulVec, dotProduct]
    _ ≤ ∑ k, |M j k * w k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, c * ρ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (hM j k)
          (le_trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm w k) hw)
          (abs_nonneg _) hc
    _ = (n : ℝ) * c * ρ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring_nf

/-- The remainder is second order in the step once `Δt‖A‖ ≤ 1`. -/
theorem aux_expRemainderBound_le {A : Mat ℝ n n} {Δt : ℝ} (hΔt : 0 ≤ Δt)
    (hAΔ : Δt * ‖A‖ ≤ 1) (η : ℕ) :
    Δt * MatExp.expRemainderBound (Δt • A) η ≤ 2 * (Δt ^ 2 * ‖A‖) := by -- --- PROOF ---
  have hnorm : ‖Δt • A‖ = Δt * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hΔt]
  have h0 : 0 ≤ ‖Δt • A‖ := norm_nonneg _
  have h1 : ‖Δt • A‖ ≤ 1 := by rw [hnorm]; exact hAΔ
  -- the power is at most the base, and the factorial at least one
  have hpow : ‖Δt • A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) ≤ ‖Δt • A‖ := by
    refine le_trans (div_le_self (by positivity) ?_) (pow_le_of_le_one h0 h1 (by omega))
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  -- and the geometric factor is at most two
  have hη : (0:ℝ) ≤ (η : ℝ) := Nat.cast_nonneg η
  have hden : (1:ℝ) / 2 ≤ 1 - ‖Δt • A‖ / ((η : ℝ) + 2) := by
    have hq : ‖Δt • A‖ / ((η : ℝ) + 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hpos : (0:ℝ) < 1 - ‖Δt • A‖ / ((η : ℝ) + 2) := by linarith
  have hgeo : (1 - ‖Δt • A‖ / ((η : ℝ) + 2))⁻¹ ≤ 2 := by
    have hcancel := inv_mul_cancel₀ (ne_of_gt hpos)
    nlinarith [mul_nonneg (inv_nonneg.mpr hpos.le) (sub_nonneg.mpr hden)]
  rw [MatExp.expRemainderBound]
  calc Δt * (‖Δt • A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)
        * (1 - ‖Δt • A‖ / ((η : ℝ) + 2))⁻¹)
      ≤ Δt * (‖Δt • A‖ * 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hpow hgeo (inv_nonneg.mpr hpos.le) h0) hΔt
    _ = 2 * (Δt ^ 2 * ‖A‖) := by rw [hnorm]; ring


/-- Order `i+1` of the step's Taylor part, against the exponential's series. -/
theorem LinearSys.aux_tail_term_le (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 ≤ Δt) (i : ℕ) :
    ‖sys.inputTerm Δt (i + 1)‖
      ≤ Δt ^ 2 * ‖toRealMat sys.A‖
        * ((Δt * ‖toRealMat sys.A‖) ^ i / Nat.factorial i) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  have hc : (0:ℝ) ≤ Δt ^ (i + 2) / (Nat.factorial (i + 2) : ℝ) := by positivity
  have hpow : ‖A ^ (i + 1)‖ ≤ ‖A‖ ^ (i + 1) := norm_pow_le' A (Nat.succ_pos i)
  have hfac : (Nat.factorial i : ℝ) ≤ (Nat.factorial (i + 2) : ℝ) :=
    Nat.cast_le.mpr (Nat.factorial_le (by omega))
  have hfac0 : (0:ℝ) < (Nat.factorial i : ℝ) := by
    exact_mod_cast Nat.factorial_pos i
  -- the coefficient out of the norm, the factorial then relaxed from `i+2` to `i`
  calc ‖sys.inputTerm Δt (i + 1)‖
      = Δt ^ (i + 2) / (Nat.factorial (i + 2) : ℝ) * ‖A ^ (i + 1)‖ := by
        rw [LinearSys.inputTerm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ Δt ^ (i + 2) / (Nat.factorial (i + 2) : ℝ) * ‖A‖ ^ (i + 1) :=
        mul_le_mul_of_nonneg_left hpow hc
    _ ≤ Δt ^ (i + 2) / (Nat.factorial i : ℝ) * ‖A‖ ^ (i + 1) := by
        refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hfac0 hfac)
          (by positivity)
    _ = Δt ^ 2 * ‖A‖ * ((Δt * ‖A‖) ^ i / Nat.factorial i) := by
        rw [mul_pow]
        field_simp
        ring


-- =======================================  MAIN THEOREM  ======================================= --

-- three pieces, each `O(Δt²)`: the orders past zero, the remainder, the series' tail
set_option maxHeartbeats 1000000 in
/-- [1, Prop. 1], outer half: one step of the outer approximation is `O(Δt²)` from the
inner approximation, hence from the exact particular solution. -/
theorem LinearSys.inputSolutionSet_dist_inputSolutionInner (sys : LinearSys 𝕋 n) {U : S n}
    {Δt ρ : ℝ} (hΔt : 0 < Δt) (hAΔ : Δt * ‖toRealMat sys.A‖ ≤ 1)
    (hne : (construct U).Nonempty) (hρ : ∀ v ∈ construct U, ‖v‖ ≤ ρ) (η : ℕ) :
    ∀ x ∈ sys.inputSolutionSet U Δt η, ∃ y ∈ sys.inputSolutionInner U Δt,
      ‖x - y‖ ≤ ρ * ‖toRealMat sys.A‖
        * (2 * (n : ℝ) + 2 + Real.exp (Δt * ‖toRealMat sys.A‖)) * Δt ^ 2 := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  obtain ⟨v₀, hv₀⟩ := hne
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (hρ _ hv₀)
  intro x hx
  obtain ⟨X, hX, R, hR, rfl⟩ := hx
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hR
  obtain ⟨M, hM, w, hw, rfl⟩ := hR
  obtain ⟨s, hs, rfl⟩ := sys.aux_exists_of_mem_sum Δt ⟨v₀, hv₀⟩ (η + 1) X hX
  refine ⟨MatExp.expIntegral A Δt *ᵥ s 0, ⟨s 0, hs 0, rfl⟩, ?_⟩
  -- the zeroth order is the only one that cancels, and what is left is three pieces
  have hsplit : (∑ i ∈ Finset.range (η + 1), sys.inputTerm Δt i *ᵥ s i) + M *ᵥ w
      - MatExp.expIntegral A Δt *ᵥ s 0
      = ((∑ i ∈ Finset.range η, sys.inputTerm Δt (i + 1) *ᵥ s (i + 1)) + M *ᵥ w)
        + (sys.inputTerm Δt 0 - MatExp.expIntegral A Δt) *ᵥ s 0 := by
    rw [Finset.sum_range_succ', Matrix.sub_mulVec]
    abel
  -- the orders `i ≥ 1`, dominated termwise by the exponential's own series
  have hP1 : ‖∑ i ∈ Finset.range η, sys.inputTerm Δt (i + 1) *ᵥ s (i + 1)‖
      ≤ Real.exp (Δt * ‖A‖) * (ρ * ‖A‖ * Δt ^ 2) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range η, ‖sys.inputTerm Δt (i + 1) *ᵥ s (i + 1)‖
        ≤ (ρ * ‖A‖ * Δt ^ 2) * ((Δt * ‖A‖) ^ i / Nat.factorial i) := by
      intro i _
      refine le_trans (Matrix.linfty_opNorm_mulVec _ _) ?_
      have hnn : (0:ℝ) ≤ Δt ^ 2 * ‖A‖ * ((Δt * ‖A‖) ^ i / Nat.factorial i) :=
        mul_nonneg (by positivity)
          (div_nonneg (pow_nonneg (mul_nonneg hΔt.le (norm_nonneg _)) i) (by positivity))
      calc ‖sys.inputTerm Δt (i + 1)‖ * ‖s (i + 1)‖
          ≤ (Δt ^ 2 * ‖A‖ * ((Δt * ‖A‖) ^ i / Nat.factorial i)) * ρ :=
            mul_le_mul (sys.aux_tail_term_le hΔt.le i) (hρ _ (hs (i + 1))) (norm_nonneg _) hnn
        _ = (ρ * ‖A‖ * Δt ^ 2) * ((Δt * ‖A‖) ^ i / Nat.factorial i) := by ring
    -- the termwise bounds summed, against the exponential's partial sum
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    calc (ρ * ‖A‖ * Δt ^ 2) * ∑ i ∈ Finset.range η, (Δt * ‖A‖) ^ i / Nat.factorial i
        ≤ (ρ * ‖A‖ * Δt ^ 2) * Real.exp (Δt * ‖A‖) :=
          mul_le_mul_of_nonneg_left
            (Real.sum_le_exp_of_nonneg (mul_nonneg hΔt.le (norm_nonneg _)) η) (by positivity)
      _ = Real.exp (Δt * ‖A‖) * (ρ * ‖A‖ * Δt ^ 2) := by ring
  -- the remainder factor, entry by entry
  have hP2 : ‖M *ᵥ w‖ ≤ (n : ℝ) * (2 * (Δt ^ 2 * ‖A‖)) * ρ := by
    refine aux_norm_mulVec_le (by positivity) hρ0 (fun j k => ?_) (hρ _ hw)
    have hent := Interval.mem_mat_iff.mp hM j k
    rw [MatExp.inputRemainder] at hent
    have hb := aux_expRemainderBound_le (A := A) hΔt.le hAΔ η
    rw [abs_le]
    exact ⟨by linarith [hent.1], by linarith [hent.2]⟩
  -- the series' own tail, which is the remainder bound at order zero
  have hP3 : ‖(sys.inputTerm Δt 0 - MatExp.expIntegral A Δt) *ᵥ s 0‖
      ≤ 2 * (Δt ^ 2 * ‖A‖) * ρ := by
    refine le_trans (Matrix.linfty_opNorm_mulVec _ _) ?_
    have hε0 : ‖Δt • A‖ / (((0:ℕ) : ℝ) + 2) < 1 := by
      have : ‖Δt • A‖ = Δt * ‖A‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hΔt.le]
      rw [this]
      norm_num
      linarith
    have heq : -(sys.inputTerm Δt 0 - MatExp.expIntegral A Δt)
        = MatExp.expIntegral A Δt
          - ∑ i ∈ Finset.range (0 + 1), ((Nat.factorial (i + 1) : ℝ)⁻¹ * Δt ^ (i + 1)) • A ^ i := by
      simp [LinearSys.inputTerm]
    -- order zero of the series is `Δt·I`, so what is left is its own tail
    have hnorm : ‖sys.inputTerm Δt 0 - MatExp.expIntegral A Δt‖ ≤ 2 * (Δt ^ 2 * ‖A‖) := by
      rw [← norm_neg, heq]
      exact le_trans (MatExp.norm_expIntegral_sub_taylor_le A hΔt.le 0 hε0)
        (aux_expRemainderBound_le hΔt.le hAΔ 0)
    exact mul_le_mul hnorm (hρ _ (hs 0)) (norm_nonneg _) (by positivity)
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (le_trans (norm_add_le _ _) (add_le_add hP1 hP2)) hP3) ?_
  ring_nf
  exact le_refl _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
