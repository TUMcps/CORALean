module

public import CORALean.ContSet.Capsule.Float.Operations.Volume
public import CORALean.ContSet.Capsule.Real.Operations.Volume
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.Sqrt
public import CORALean.Global.Float.InverseTrig
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# `Capsule.volume` bounds the volume of the nominal capsule

Each `ωₖ = π^(k/2) / Γ(k/2 + 1)` obeys `ω₀ = 1`, `ω₁ = 2` and `ω_{k+2} = 2π / (k + 2) · ωₖ`
(`Real.Gamma_add_one`, `Real.Gamma_one_half_eq`), so the rounded-up recursion `Capsule.ballVol`
bounds it from above. The radius power is bounded by `le_powUp`, the norm of the generator by
`norm₂_le_normUp`, and `π` by four times `acosUp` of `0`. An upper bound of CORA's formula.

## Inputs
* `p` – precision of acos
* `k` – Newton steps for the root
* `C` – capsule

## Hypotheses
* none

## Conclusion
* the real `Capsule.volume` of the nominal capsule is at most the value returned
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_ballVol_step (k : ℕ) : -- --- CONCL ---
    Real.pi ^ (((k + 2 : ℕ) : ℝ) / 2) / Real.Gamma (((k + 2 : ℕ) : ℝ) / 2 + 1)
      = 2 * Real.pi / ((k : ℝ) + 2) *
        (Real.pi ^ ((k : ℝ) / 2) / Real.Gamma ((k : ℝ) / 2 + 1)) := by -- --- PROOF ---
  -- `Γ(x + 1) = x Γ(x)` and `π^(x + 1) = π^x π`
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hg : Real.Gamma ((k : ℝ) / 2 + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have e1 : (((k + 2 : ℕ) : ℝ) / 2 + 1) = ((k : ℝ) / 2 + 1) + 1 := by push_cast; ring
  have e2 : (((k + 2 : ℕ) : ℝ) / 2) = (k : ℝ) / 2 + 1 := by push_cast; ring
  rw [e1, e2, Real.Gamma_add_one (by positivity), Real.rpow_add_one Real.pi_pos.ne']
  field_simp

private theorem aux_ballVol_nonneg (k : ℕ) :
    0 ≤ Real.pi ^ ((k : ℝ) / 2) / Real.Gamma ((k : ℝ) / 2 + 1) :=
  div_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
    (Real.Gamma_pos_of_pos (by positivity)).le

private theorem aux_le_ballVol {twoPi : 𝕋} (h : 2 * Real.pi ≤ toReal twoPi)
    (k : ℕ) : -- --- CONCL ---
    Real.pi ^ ((k : ℝ) / 2) / Real.Gamma ((k : ℝ) / 2 + 1)
        ≤ toReal (Capsule.ballVol twoPi k) ∧
      Real.pi ^ (((k + 1 : ℕ) : ℝ) / 2) / Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1)
        ≤ toReal (Capsule.ballVol twoPi (k + 1)) := by -- --- PROOF ---
  induction k with
  | zero =>
    -- `ω₀ = 1` and `ω₁ = Γ(1/2) / Γ(3/2) ... = 2`
    refine ⟨by simp [Capsule.ballVol, toReal_one], ?_⟩
    have h1 : Real.Gamma (((1 : ℕ) : ℝ) / 2 + 1) = Real.sqrt Real.pi / 2 := by
      have : (((1 : ℕ) : ℝ) / 2 + 1) = (1 / 2 : ℝ) + 1 := by norm_num
      rw [this, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
    have h2 : Real.pi ^ (((1 : ℕ) : ℝ) / 2) = Real.sqrt Real.pi := by
      rw [Real.sqrt_eq_rpow]; norm_num
    have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    have : Real.pi ^ (((0 + 1 : ℕ) : ℝ) / 2) / Real.Gamma (((0 + 1 : ℕ) : ℝ) / 2 + 1) = 2 := by
      simp only [zero_add]; rw [h1, h2]; field_simp
    rw [this]
    simp only [Capsule.ballVol]
    have := add_le_addUp (one : 𝕋) one
    rw [toReal_one] at this
    linarith
  | succ k ih =>
    -- the step `ω_{k+2} = 2π / (k + 2) ωₖ`, rounded up factor by factor
    refine ⟨ih.2, ?_⟩
    rw [show ((k + 1 + 1 : ℕ) : ℝ) = (((k : ℕ) + 2 : ℕ) : ℝ) by push_cast; ring]
    rw [aux_ballVol_step k]
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    -- the rounded-up factor `2π / (k + 2)` is above the real one, in both branches
    have hq : 2 * Real.pi / ((k : ℝ) + 2) ≤
        toReal (if ltStrict (zero : 𝕋) (intDown ((k : ℤ) + 2)) then
          divUp twoPi (intDown ((k : ℤ) + 2)) else twoPi) := by
      split_ifs with hl
      · have hd := toReal_lt_of_ltStrict hl
        rw [toReal_zero] at hd
        have hdi := (intDown_le_intUp (𝕋 := 𝕋) ((k : ℤ) + 2)).1
        push_cast at hdi
        refine le_trans ?_ (div_le_divUp twoPi _ hd)
        calc 2 * Real.pi / ((k : ℝ) + 2) ≤ toReal twoPi / ((k : ℝ) + 2) :=
              div_le_div_of_nonneg_right h hk.le
          _ ≤ toReal twoPi / toReal (intDown ((k : ℤ) + 2)) :=
              div_le_div_of_nonneg_left (by linarith [Real.pi_pos]) hd hdi
      · calc 2 * Real.pi / ((k : ℝ) + 2) ≤ 2 * Real.pi := by
              apply div_le_self (by linarith [Real.pi_pos])
              linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
          _ ≤ _ := h
    -- the product with the previous volume, rounded up
    simp only [Capsule.ballVol]
    exact le_trans (mul_le_mul hq ih.1 (aux_ballVol_nonneg k)
      (le_trans (by positivity) hq)) (mul_le_mulUp _ _)

private theorem aux_twoPi (p k : ℕ) : -- --- CONCL ---
    2 * Real.pi ≤ toReal (addUp (addUp (acosUp p k (zero : 𝕋)) (acosUp p k zero))
      (addUp (acosUp p k zero) (acosUp p k zero))) := by -- --- PROOF ---
  have h := le_acosUp (𝕋 := 𝕋) p k zero
  rw [toReal_zero, Real.arccos_zero] at h
  have a1 := add_le_addUp (acosUp p k (zero : 𝕋)) (acosUp p k zero)
  have a2 := add_le_addUp (addUp (acosUp p k (zero : 𝕋)) (acosUp p k zero))
    (addUp (acosUp p k zero) (acosUp p k zero))
  have a3 := add_le_addUp (acosUp p k (zero : 𝕋)) (acosUp p k zero)
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.volume_le (p k : ℕ) (C : Capsule 𝕋 n) : -- --- CONCL ---
    CORALean.Real.Capsule.volume C.nominal
      ≤ ENNReal.ofReal (toReal (C.volume p k)) := by -- --- PROOF ---
  -- an empty capsule or `n = 0` has volume `0`; otherwise bound each factor of the formula
  by_cases hz : n = 0 ∨ C.nominal.r < 0
  · simp only [CORALean.Real.Capsule.volume, if_pos hz]; exact bot_le
  rw [CORALean.Real.Capsule.volume, if_neg hz]
  rw [not_or, not_lt] at hz
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz.1
  have hr : 0 ≤ toReal C.r := hz.2
  have hr' : toReal C.r ≤ toReal (maximum zero C.r) := by
    rw [toReal_maximum]; exact le_max_right _ _
  have hn : m + 1 ≠ 0 := Nat.succ_ne_zero m
  -- the factors: ball volumes, radius powers and the norm of the generator
  have hb := aux_le_ballVol (aux_twoPi (𝕋 := 𝕋) p k) m
  have hP := fun j => le_powUp hr hr' j
  have hg : CORALean.norm₂ (C.nominal.g) ≤ toReal (normUp k C.g) :=
    norm₂_le_normUp k fun j => le_of_eq (rfl)
  simp only [Capsule.volume, if_neg hn, Nat.succ_sub_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (((m + 1 : ℕ) : ℝ) - 1) = (m : ℝ) := by push_cast; ring
  have hbm := hb.1
  have hbn := hb.2
  have hp1 := hP (m + 1)
  have hp0 := hP m
  have hq : 0 ≤ Real.pi ^ ((m : ℝ) / 2) / Real.Gamma ((m : ℝ) / 2 + 1) := aux_ballVol_nonneg m
  have hq1 : 0 ≤ Real.pi ^ (((m + 1 : ℕ) : ℝ) / 2) /
      Real.Gamma (((m + 1 : ℕ) : ℝ) / 2 + 1) := aux_ballVol_nonneg (m + 1)
  have hpow0 : 0 ≤ toReal C.r ^ m := pow_nonneg hr m
  have hpow1 : 0 ≤ toReal C.r ^ (m + 1) := pow_nonneg hr _
  have hnorm : 0 ≤ CORALean.norm₂ C.nominal.g := Real.sqrt_nonneg _
  -- multiply and add the bounds, rounded up as in `Capsule.volume`
  have t1 := le_trans (mul_le_mul hbn hp1 hpow1 (le_trans hq1 hbn)) (mul_le_mulUp _ _)
  have t0 := le_trans (mul_le_mul hbm hp0 hpow0 (le_trans hq hbm)) (mul_le_mulUp _ _)
  have h2 : (2 : ℝ) ≤ toReal (addUp (one : 𝕋) one) := by
    have := add_le_addUp (one : 𝕋) one
    rw [toReal_one] at this; linarith
  have t2 := le_trans (mul_le_mul h2 hg hnorm (by linarith)) (mul_le_mulUp _ _)
  have t3 := le_trans (mul_le_mul t0 t2 (mul_nonneg (by norm_num) hnorm)
    (le_trans (mul_nonneg hq hpow0) t0)) (mul_le_mulUp _ _)
  have t4 := add_le_add t1 t3
  refine le_trans ?_ (le_trans t4 (add_le_addUp _ _))
  simp only [Capsule.nominal, e]
  exact le_of_eq (by simp [CORALean.norm₂])

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
