module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AffineDynamicsErrorLe

@[expose] public section

/-!
# `affineDynamicsError` converges to zero superlinearly

Eventually, as `Δt → 0⁺`, `affineDynamicsError` is under one linear bound `K · Δt` — [1,
Lemma 3]'s asymptotic claim, [1, Alg. 2]'s tuning search relies on.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Eventually, as `Δt → 0⁺`, `affineDynamicsError` is under one linear bound `K · Δt`: once
`Δt ≤ 1` and `Δt‖A‖ ≤ 1`, every `Δt`-dependent factor of `affineDynamicsErrorBound` is under
`Δt` times a `Δt`-free constant. -/
theorem MatExp.exists_affineDynamicsError_le_const_mul (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (η : ℕ) :
    ∃ K : ℝ, ∀ᶠ Δt : ℝ in 𝓝[>] (0:ℝ),
      MatExp.affineDynamicsError A H ũ Δt η ≤ K * Δt := by -- --- PROOF ---
  -- the three `Δt`-free constants the bound's three `Δt`-dependent factors are traded for
  set CE := 2 * (‖A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) with hCEdef
  set cF := ‖A‖ ^ 2 * Real.exp 1 + CE with hcFdef
  set cG := Real.exp 1 - 1 + CE with hcGdef
  have hCE0 : (0:ℝ) ≤ CE := by rw [hCEdef]; positivity
  have hSumH : (0:ℝ) ≤ ∑ j, H.absBound j := Finset.sum_nonneg fun j _ => by
    rw [Zonotope.absBound]; positivity
  have hSumU : (0:ℝ) ≤ ∑ j, |ũ j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hSumG : (0:ℝ) ≤ ∑ l, ∑ j, |H.G l j| :=
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨4 * (n:ℝ) * (cF * ∑ j, H.absBound j + cG * ∑ j, |ũ j|)
    + Real.sqrt H.h * ((n:ℝ) * (‖A‖ * Real.exp 1) * ∑ l, ∑ j, |H.G l j|), ?_⟩
  -- the two conditions everything below runs under, each holding eventually
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hev1 : ∀ᶠ Δt : ℝ in 𝓝[>] (0:ℝ), Δt ≤ 1 := hid.eventually_le_const (by norm_num)
  have hev2 : ∀ᶠ Δt : ℝ in 𝓝[>] (0:ℝ), Δt * ‖A‖ ≤ 1 := by
    have h : Tendsto (fun Δt : ℝ => Δt * ‖A‖) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using hid.mul_const ‖A‖
    exact h.eventually_le_const (by norm_num)
  filter_upwards [hev1, hev2, self_mem_nhdsWithin] with Δt hΔt1 hAn hmem
  have hΔtpos : (0:ℝ) < Δt := hmem
  have hx0 : (0:ℝ) ≤ Δt * ‖A‖ := mul_nonneg hΔtpos.le (norm_nonneg _)
  have hnorm : ‖Δt • A‖ = Δt * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hΔtpos]
  have hηnn : (0:ℝ) ≤ (η:ℝ) := Nat.cast_nonneg η
  have hε : ‖Δt • A‖ / ((η : ℝ) + 2) < 1 := by
    rw [hnorm, div_lt_one (by positivity)]
    linarith
  -- the exponential's remainder, at the order `Lemma 1` gives it
  have hERB : MatExp.expRemainderBound (Δt • A) η ≤ CE * Δt := by
    have hq : Δt * ‖A‖ / ((η:ℝ) + 2) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (η:ℝ) + 2)]
      linarith
    have hd : (0:ℝ) < 1 - Δt * ‖A‖ / ((η:ℝ) + 2) := by linarith
    have hprod : (1 - Δt * ‖A‖ / ((η:ℝ) + 2))⁻¹ * (1 - Δt * ‖A‖ / ((η:ℝ) + 2)) = 1 :=
      inv_mul_cancel₀ (ne_of_gt hd)
    have hinv : (1 - Δt * ‖A‖ / ((η:ℝ) + 2))⁻¹ ≤ 2 := by
      nlinarith [inv_nonneg.mpr hd.le]
    -- one power of the step survives the `η + 1` the numerator carries
    have hpow : (Δt * ‖A‖) ^ (η + 1) ≤ Δt * ‖A‖ ^ (η + 1) := by
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg A) _)
      calc Δt ^ (η + 1) = Δt ^ η * Δt := by ring
        _ ≤ 1 * Δt := mul_le_mul_of_nonneg_right (pow_le_one₀ hΔtpos.le hΔt1) hΔtpos.le
        _ = Δt := one_mul _
    have hfac : (0:ℝ) < (Nat.factorial (η + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos (η + 1)
    rw [MatExp.expRemainderBound, hnorm, hCEdef]
    calc (Δt * ‖A‖) ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)
          * (1 - Δt * ‖A‖ / ((η:ℝ) + 2))⁻¹
        ≤ Δt * ‖A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) * 2 :=
          mul_le_mul (by gcongr) hinv (inv_nonneg.mpr hd.le) (by positivity)
      _ = 2 * (‖A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * Δt := by ring
  -- the correction's own finite part, second order in the step
  have hexpx : Real.exp (Δt * ‖A‖) ≤ Real.exp 1 := Real.exp_le_exp.mpr hAn
  have haux : Real.exp (Δt * ‖A‖) - 1 ≤ (Δt * ‖A‖) * Real.exp (Δt * ‖A‖) := by
    have h := Real.add_one_le_exp (-(Δt * ‖A‖))
    have hmul : (-(Δt * ‖A‖) + 1) * Real.exp (Δt * ‖A‖)
        ≤ Real.exp (-(Δt * ‖A‖)) * Real.exp (Δt * ‖A‖) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
    linarith
  have hquad : Real.exp (Δt * ‖A‖) - 1 - Δt * ‖A‖
      ≤ (Δt * ‖A‖) ^ 2 * Real.exp (Δt * ‖A‖) := by
    linarith [mul_le_mul_of_nonneg_left haux hx0]
  -- second order in the step is under first order once the step is itself under one
  have hsq : (Δt * ‖A‖) ^ 2 * Real.exp (Δt * ‖A‖) ≤ Δt * (‖A‖ ^ 2 * Real.exp 1) := by
    have hd2 : Δt ^ 2 ≤ Δt :=
      calc Δt ^ 2 = Δt * Δt := pow_two Δt
        _ ≤ 1 * Δt := mul_le_mul_of_nonneg_right hΔt1 hΔtpos.le
        _ = Δt := one_mul Δt
    calc (Δt * ‖A‖) ^ 2 * Real.exp (Δt * ‖A‖) = Δt ^ 2 * (‖A‖ ^ 2 * Real.exp (Δt * ‖A‖)) := by
          ring
      _ ≤ Δt ^ 2 * (‖A‖ ^ 2 * Real.exp 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpx (sq_nonneg _)) (sq_nonneg Δt)
      _ ≤ Δt * (‖A‖ ^ 2 * Real.exp 1) := mul_le_mul_of_nonneg_right hd2 (by positivity)
  have hρF : Real.exp (Δt * ‖A‖) - 1 - Δt * ‖A‖ + MatExp.expRemainderBound (Δt • A) η
      ≤ cF * Δt := by rw [hcFdef]; linarith [hquad.trans hsq]
  -- the integrated correction pays one `Δt` up front, so its own factors need only be bounded
  have hρG : Δt * (Real.exp (Δt * ‖A‖) - 1) + Δt * MatExp.expRemainderBound (Δt • A) η
      ≤ cG * Δt := by
    have h1 : Δt * (Real.exp (Δt * ‖A‖) - 1) ≤ Δt * (Real.exp 1 - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hΔtpos.le
    have h2 : Δt * MatExp.expRemainderBound (Δt • A) η ≤ Δt * CE := by
      refine mul_le_mul_of_nonneg_left (hERB.trans ?_) hΔtpos.le
      calc CE * Δt ≤ CE * 1 := mul_le_mul_of_nonneg_left hΔt1 hCE0
        _ = CE := mul_one CE
    rw [hcGdef]; linarith
  -- and the generators the step moves
  have hgen : (n:ℝ) * (Δt * ‖A‖ * Real.exp (Δt * ‖A‖)) * ∑ l, ∑ j, |H.G l j|
      ≤ (n:ℝ) * (Δt * (‖A‖ * Real.exp 1)) * ∑ l, ∑ j, |H.G l j| := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)) hSumG
    calc Δt * ‖A‖ * Real.exp (Δt * ‖A‖) ≤ Δt * ‖A‖ * Real.exp 1 :=
          mul_le_mul_of_nonneg_left hexpx hx0
      _ = Δt * (‖A‖ * Real.exp 1) := by ring
  refine (MatExp.affineDynamicsError_le A H ũ hΔtpos.le hε).trans ?_
  rw [MatExp.affineDynamicsErrorBound]
  refine le_trans (add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right hρF hSumH)
      (mul_le_mul_of_nonneg_right hρG hSumU)) (by positivity))
    (mul_le_mul_of_nonneg_left hgen (Real.sqrt_nonneg _))) (le_of_eq (by ring))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
