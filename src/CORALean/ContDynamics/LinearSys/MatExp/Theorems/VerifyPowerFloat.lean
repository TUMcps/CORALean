module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyPowerFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `MatExp.verifyPowerFloat` encloses `Aⁱ/i!`

By induction on `i`: the identity is the stored identity, a product of a box with the point `A`
is `Interval.matMul_outer`, and the division by `i + 1` stays between the corners because
`1 ≤ max 1 (nsmulDown (i+1) 1) ≤ i + 1 ≤ nsmulUp (i+1) 1` and a quotient by a positive divisor is
monotone in it with the sign of the dividend.

## Inputs
* `A` – float system matrix
* `i` – power

## Hypotheses
* none

## Conclusion
* `Aⁱ/i!` lies in the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored identity block reads back as the real identity matrix. -/
private theorem MatExp.aux_toRealMat_diagonalBlock_one :
    toRealMat (diagonalBlock fun _ : Fin n => (one : 𝕋)) = (1 : Mat ℝ n n) := by
  funext i j
  rw [toRealMat, toReal_diagonalBlock]
  simp [toRealVec, toReal_one, Matrix.one_apply, Matrix.diagonal_apply]

/-- A member of the box divided by `k ≥ 1` lies in the divided box. -/
private theorem MatExp.aux_div_mem_step_verifyDivNatFloat (P : Interval (Mat 𝕋 n n)) {k : ℕ}
    (hk : 1 ≤ k) {X : Mat ℝ n n} (hX : X ∈ P.toSet) : -- --- CONCL ---
    ((k : ℝ)⁻¹ • X) ∈ (MatExp.step_verifyDivNatFloat P k).toSet := by -- --- PROOF ---
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  -- the divisors: `1 ≤ dLo ≤ k ≤ dHi`
  set dLo : 𝕋 := maximum one (nsmulDown k one)
  set dHi : 𝕋 := nsmulUp k one
  have hdLo1 : 1 ≤ toReal dLo := by
    rw [toReal_maximum, toReal_one]; exact le_max_left _ _
  have hdLok : toReal dLo ≤ k := by
    have h := nsmulDown_le k (one : 𝕋)
    rw [toReal_one, mul_one] at h
    rw [toReal_maximum, toReal_one]; exact max_le hk1 h
  have hdHik : (k : ℝ) ≤ toReal dHi := by
    have h := le_nsmulUp k (one : 𝕋)
    rwa [toReal_one, mul_one] at h
  -- a real number over `k` is between its quotients by the two divisors
  have hdLo0 : 0 < toReal dLo := by linarith
  have hdHi0 : 0 < toReal dHi := by linarith
  -- a real number over `k` is between its quotients by the two divisors
  have hlo : ∀ a x : ℝ, a ≤ x → min (a / toReal dLo) (a / toReal dHi) ≤ (k : ℝ)⁻¹ * x := by
    intro a x hax
    have hx : a / k ≤ (k : ℝ)⁻¹ * x := by
      rw [inv_mul_eq_div]; exact div_le_div_of_nonneg_right hax hk0.le
    rcases le_total 0 a with ha | ha
    · exact le_trans (min_le_right _ _)
        (le_trans (div_le_div_of_nonneg_left ha hk0 hdHik) hx)
    · refine le_trans (min_le_left _ _) (le_trans ?_ hx)
      rw [div_le_div_iff₀ hdLo0 hk0]; nlinarith
  have hhi : ∀ b x : ℝ, x ≤ b → (k : ℝ)⁻¹ * x ≤ max (b / toReal dLo) (b / toReal dHi) := by
    intro b x hxb
    have hx : (k : ℝ)⁻¹ * x ≤ b / k := by
      rw [inv_mul_eq_div]; exact div_le_div_of_nonneg_right hxb hk0.le
    rcases le_total 0 b with hb | hb
    · exact le_trans hx (le_trans (div_le_div_of_nonneg_left hb hdLo0 hdLok)
        (le_max_left _ _))
    · refine le_trans hx (le_trans ?_ (le_max_right _ _))
      rw [div_le_div_iff₀ hk0 hdHi0]; nlinarith
  -- entry by entry, each rounded quotient on its side
  refine Interval.mem_mat_iff.mpr fun j l => ?_
  obtain ⟨h1, h2⟩ := Interval.mem_mat_iff.mp hX j l
  simp only [MatExp.step_verifyDivNatFloat, Matrix.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [toReal_minimum]
    refine le_trans (min_le_min (divDown_le_div _ _ hdLo0) (divDown_le_div _ _ hdHi0)) ?_
    exact hlo _ _ h1
  · rw [toReal_maximum]
    refine le_trans ?_ (max_le_max (div_le_divUp _ _ hdLo0) (div_le_divUp _ _ hdHi0))
    exact hhi _ _ h2


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.pow_div_factorial_mem_verifyPowerFloat (A : Mat 𝕋 n n) (i : ℕ) : -- --- CONCL ---
    ((Nat.factorial i : ℝ)⁻¹ • toRealMat A ^ i)
      ∈ (MatExp.verifyPowerFloat A i).toSet := by -- --- PROOF ---
  induction i with
  | zero =>
    rw [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      ← MatExp.aux_toRealMat_diagonalBlock_one (𝕋 := 𝕋)]
    exact Interval.mem_point (diagonalBlock fun _ : Fin n => (one : 𝕋))
  | succ i ih =>
    have hA : toRealMat A ∈ (Interval.point A).toSet := Interval.mem_point A
    have hprod := Interval.matMul_outer _ _ ih hA
    have hdiv := MatExp.aux_div_mem_step_verifyDivNatFloat _ (k := i + 1) (by omega) hprod
    show _ ∈ (MatExp.step_verifyDivNatFloat _ (i + 1)).materialiseMat.toSet
    rw [Interval.materialiseMat_eq]
    convert hdiv using 1
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ, smul_mul_assoc, smul_smul, mul_inv]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
