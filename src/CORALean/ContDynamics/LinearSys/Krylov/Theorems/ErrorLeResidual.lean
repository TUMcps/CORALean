module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorLeResidualIntegral
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpApplyLastLe

@[expose] public section

/-!
# The Krylov error for every matrix: the residual, the growth rate and the product bound

[1, Thm. 3] without the nonexpansiveness `W(A) ⊆ ℂ⁻`, which [1] assumes and CORA's order test
relies on (`jawecki_bound_cora_counterexample`). Let `μ` bound the real part of the Rayleigh
quotients of both `A` and `T`. Then `A - μ` and `T - μ` satisfy the Krylov identity with the same
residual and have their fields of values in `ℂ⁻`, so `Krylov.error_le_residual_integral` applies,
`|(e^{s(T-μ)})_{m,1}|` is at most `|γ|s^{m-1}/(m-1)!` by `Krylov.norm_exp_apply_last_le`
(a shift of the diagonal keeps the subdiagonal and the Hessenberg shape), and `e^{tA} = e^{tμ}
e^{t(A-μ)}`. With `γ = ∏ T_{j+1,j}` the error is at most `e^{μt}(|τ|‖w‖|γ| t^k/k! + d t)`, `k` the
order. For `μ ≤ 0` it is [1]'s bound plus the residual's share; a `μ > 0` costs the factor `e^{μt}`.

## Inputs
* `A` – matrix
* `V` – Krylov basis
* `T` – Hessenberg matrix
* `τ` – next subdiagonal entry
* `w` – next vector
* `Δ` – residual of the Krylov identity
* `d` – bound on the residual's operator norm
* `μ` – upper bound on the fields of values
* `t` – time

## Hypotheses
* `hK` – Krylov identity holds up to the residual
* `hΔ` – residual bounded
* `hH` – Hessenberg matrix upper Hessenberg
* `hA` – real part of the Rayleigh quotient of the matrix at most the growth rate
* `hT` – real part of the Rayleigh quotient of the Hessenberg matrix at most the growth rate
* `ht` – time nonnegative

## Conclusion
* the Krylov error is at most the product bound with the growth factor, plus the residual's share

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `e^{tM} = e^{tμ}e^{t(M - μ)}`. -/
private theorem aux_exp_shift {k : ℕ} (M : Mat ℂ k k) (μ t : ℝ) : -- --- CONCL ---
    exp (t • M) = ((Real.exp (t * μ) : ℝ) : ℂ) • exp (t • (M - (μ : ℂ) • 1)) := by -- --- PROOF ---
  have hM : t • M = t • (M - (μ : ℂ) • 1) + ((t * μ : ℝ) : ℂ) • (1 : Mat ℂ k k) := by
    ext i j
    by_cases h : i = j
    · simp [h, Matrix.smul_apply]
      ring
    · simp [h, Matrix.smul_apply]
  have hcomm : Commute (t • (M - (μ : ℂ) • 1)) (((t * μ : ℝ) : ℂ) • (1 : Mat ℂ k k)) :=
    (Commute.one_right _).smul_right _
  have hscal : exp (((t * μ : ℝ) : ℂ) • (1 : Mat ℂ k k)) =
      ((Real.exp (t * μ) : ℝ) : ℂ) • (1 : Mat ℂ k k) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal]
    ext i j
    by_cases h : i = j
    · simp [h, Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
    · simp [h]
  rw [hM, Matrix.exp_add_of_commute _ _ hcomm, hscal, Matrix.mul_smul, Matrix.mul_one]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Under `A V = V T + τ w e_m* + Δ`, `‖Δ x‖₂ ≤ d‖x‖₂`, upper Hessenberg `T`, `Re(x*Ax) ≤ μx*x`,
`Re(x*Tx) ≤ μx*x` and `t ≥ 0`: `‖e^{tA}Ve₁ - V e^{tT}e₁‖₂ ≤ e^{μt}(|τ|‖w‖|γ|t^{m+1}/(m+1)! +
d t)`, `γ = ∏ T_{j+1,j}`; `V` has `m + 1` columns. -/
theorem Krylov.error_le_residual (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ : ℂ) (w : Fin n → ℂ) (Δ : Mat ℂ n (m + 1)) (d μ : ℝ)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1) + Δ)
    (hΔ : ∀ x : Fin (m + 1) → ℂ,
      ‖(WithLp.toLp 2 (Δ *ᵥ x) : EuclideanSpace ℂ (Fin n))‖ ≤
        d * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin (m + 1)))‖)
    (hH : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T i k = 0)
    (hA : ∀ x : Fin n → ℂ, (star x ⬝ᵥ (A *ᵥ x)).re ≤ μ * (star x ⬝ᵥ x).re)
    (hT : ∀ x : Fin (m + 1) → ℂ, (star x ⬝ᵥ (T *ᵥ x)).re ≤ μ * (star x ⬝ᵥ x).re) {t : ℝ}
    (ht : 0 ≤ t) : -- --- CONCL ---
    let v := V *ᵥ Pi.single 0 1
    ‖(WithLp.toLp 2 (exp (t • A) *ᵥ v - V *ᵥ (exp (t • T) *ᵥ Pi.single 0 1)) :
        EuclideanSpace ℂ (Fin n))‖ ≤
      Real.exp (t * μ) * (‖τ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ *
        (‖∏ j : Fin m, T j.succ j.castSucc‖ * t ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) +
          d * t) := by -- --- PROOF ---
  intro v
  set A' : Mat ℂ n n := A - (μ : ℂ) • 1 with hA'
  set T' : Mat ℂ (m + 1) (m + 1) := T - (μ : ℂ) • 1 with hT'
  -- the shifted pair keeps the Krylov identity and has its fields of values in `ℂ⁻`
  have hK' : A' * V = V * T' + τ • vecMulVec w (Pi.single (Fin.last m) 1) + Δ := by
    rw [hA', hT', Matrix.sub_mul, Matrix.mul_sub, hK]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    abel
  have hrq : ∀ {k : ℕ} (M : Mat ℂ k k) (x : Fin k → ℂ),
      (star x ⬝ᵥ ((M - (μ : ℂ) • 1) *ᵥ x)).re = (star x ⬝ᵥ (M *ᵥ x)).re - μ * (star x ⬝ᵥ x).re := by
    intro k M x
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
  have hA'neg : ∀ x : Fin n → ℂ, (star x ⬝ᵥ (A' *ᵥ x)).re ≤ 0 := fun x => by
    rw [hA', hrq]; linarith [hA x]
  have hT'neg : ∀ x : Fin (m + 1) → ℂ, (star x ⬝ᵥ (T' *ᵥ x)).re ≤ 0 := fun x => by
    rw [hT', hrq]; linarith [hT x]
  have hmain := Krylov.error_le_residual_integral A' V T' τ w Δ d hK' hΔ hA'neg hT'neg ht
  -- the subdiagonal and the Hessenberg shape are those of `T`
  have hH' : ∀ i k : Fin (m + 1), (k : ℕ) + 1 < i → T' i k = 0 := by
    intro i k hik
    have hne : i ≠ k := fun h => by subst h; omega
    simp [hT', hH i k hik, hne]
  have hsub : ∀ j : Fin m, T' j.succ j.castSucc = T j.succ j.castSucc := by
    intro j
    have hne : j.succ ≠ j.castSucc := fun h => by
      have := congrArg Fin.val h; simp at this
    simp [hT', hne]
  have hδ : ∀ s : ℝ, 0 ≤ s → ‖exp (s • T') (Fin.last m) 0‖ ≤
      ‖∏ j : Fin m, T j.succ j.castSucc‖ * s ^ m / (Nat.factorial m : ℝ) := by
    intro s hs
    have h := Krylov.norm_exp_apply_last_le m T' 1 hH' (by simpa using hT'neg) (by simp) hs
    simpa [hsub] using h
  -- the integral of `|δ'|`
  set c := ‖τ‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ with hc
  have hδc : Continuous fun s : ℝ => ‖exp (s • T') (Fin.last m) 0‖ :=
    ((exp_continuous.comp (continuous_id.smul continuous_const)).matrix_elem _ _).norm
  have hint : ∫ s in (0 : ℝ)..t, ‖exp (s • T') (Fin.last m) 0‖ ≤
      ‖∏ j : Fin m, T j.succ j.castSucc‖ * t ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
    have h1 : ∫ s in (0 : ℝ)..t, ‖exp (s • T') (Fin.last m) 0‖ ≤
        ∫ s in (0 : ℝ)..t, ‖∏ j : Fin m, T j.succ j.castSucc‖ / (Nat.factorial m : ℝ) * s ^ m :=
      intervalIntegral.integral_mono_on ht (hδc.intervalIntegrable _ _)
        ((continuous_const.mul (continuous_pow m)).intervalIntegrable _ _) fun s hs =>
        (hδ s hs.1).trans (le_of_eq (by ring))
    refine h1.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have hc0 : 0 ≤ c := by positivity
  have hmain' : ‖(WithLp.toLp 2 (exp (t • A') *ᵥ v - V *ᵥ (exp (t • T') *ᵥ Pi.single 0 1)) :
      EuclideanSpace ℂ (Fin n))‖ ≤ c * (‖∏ j : Fin m, T j.succ j.castSucc‖ * t ^ (m + 1) /
        (Nat.factorial (m + 1) : ℝ)) + d * t :=
    hmain.trans (add_le_add_left (mul_le_mul_of_nonneg_left hint hc0) _)
  -- `e^{tA}v - V e^{tT}e₁ = e^{tμ}(e^{tA'}v - V e^{tT'}e₁)`
  have hshift : exp (t • A) *ᵥ v - V *ᵥ (exp (t • T) *ᵥ Pi.single 0 1) =
      ((Real.exp (t * μ) : ℝ) : ℂ) •
        (exp (t • A') *ᵥ v - V *ᵥ (exp (t • T') *ᵥ Pi.single 0 1)) := by
    rw [hA', hT', aux_exp_shift A μ t, aux_exp_shift T μ t]
    simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_sub]
  rw [hshift, WithLp.toLp_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left hmain' (Real.exp_pos _).le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
