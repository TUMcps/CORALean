module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.DissipationOfHinfLmi
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The `H∞` observer gain

[1, Thm. 1]: if `P ≻ 0` and `Y` satisfy Eq. 16 of [1, Thm. 1], then at `L = P⁻¹ Y` the error system
`e_{k+1} = A_e e_k + B_e d_k`, `A_e = A - LC`, `B_e = [E  -LF]` [1, Eq. 15], is stable and
`‖G_ed‖∞ < γ` for `G_ed(z) = (zI - A_e)⁻¹ B_e`. Stated without a transfer-function library:
every eigenvalue of `A_e` lies in the open unit disc (so `zI - A_e` is invertible on `|z| = 1`),
and some `γ' < γ` has `‖e‖ ≤ γ' ‖d‖` whenever `z e = A_e e + B_e d`, `|z| = 1`, which is
`σ_max(G_ed(z)) ≤ γ'` on the unit circle. The paper goes through the bounded real lemma
[1, Lemma 1]; here the dissipation inequality its Eq. 17 (`dissipation_of_hinfLmi`) is applied to
the real and imaginary parts of `(e, d)`, where `|z| = 1` turns `(z e)ᴴ P (z e)` into `eᴴ P e`.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `E` – disturbance matrix
* `F` – noise matrix
* `P` – Lyapunov matrix
* `Y` – gain variable
* `γ` – attenuation level

## Hypotheses
* `hγ` – attenuation level positive
* `hP` – Lyapunov matrix positive definite
* `h` – the design inequality holds

## Conclusion
* the error system is stable with gain below `γ`

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nw nv : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- a real matrix acts on real and imaginary parts separately
theorem LinearSysDT.aux_re_im_mulVec {m k : ℕ} (M : Mat ℝ m k) (x : Fin k → ℂ) :
    (fun i => ((M.map Complex.ofReal) *ᵥ x) i |>.re) = M *ᵥ (fun j => (x j).re) ∧
      (fun i => ((M.map Complex.ofReal) *ᵥ x) i |>.im) = M *ᵥ (fun j => (x j).im) := by
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩ <;>
    simp [mulVec, dotProduct, Complex.re_sum, Complex.im_sum]

-- the squared norm of a complex vector is that of its real and imaginary parts
theorem LinearSysDT.aux_sum_sq_norm {k : ℕ} (x : Fin k → ℂ) :
    ∑ i, ‖x i‖ ^ 2 = (fun j => (x j).re) ⬝ᵥ (fun j => (x j).re) +
      (fun j => (x j).im) ⬝ᵥ (fun j => (x j).im) := by
  simp only [dotProduct, ← Finset.sum_add_distrib, Complex.sq_norm, Complex.normSq_apply]

-- its Eq. 17 on the real and imaginary parts of a complex solution of `z e = A_e e + B_e d`
theorem LinearSysDT.aux_complex_dissipation (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ n nw)
    (F : Mat ℝ ny nv) (P : Mat ℝ n n) (Y : Mat ℝ n ny) (γ ε : ℝ) (hP : P.PosDef)
    (hd : ∀ (a : Vec ℝ n) (b : Vec ℝ nw) (c : Vec ℝ nv),
      let q := (A - P⁻¹ * Y * C) *ᵥ a + E *ᵥ b - (P⁻¹ * Y * F) *ᵥ c
      q ⬝ᵥ (P *ᵥ q) + a ⬝ᵥ a - a ⬝ᵥ (P *ᵥ a) - γ ^ 2 * (b ⬝ᵥ b + c ⬝ᵥ c) ≤
        -ε * (a ⬝ᵥ a + b ⬝ᵥ b + c ⬝ᵥ c))
    (z : ℂ) (e : Fin n → ℂ) (dw : Fin nw → ℂ) (dv : Fin nv → ℂ)
    (h : z • e = (A - P⁻¹ * Y * C).map Complex.ofReal *ᵥ e + E.map Complex.ofReal *ᵥ dw -
      (P⁻¹ * Y * F).map Complex.ofReal *ᵥ dv) : -- --- CONCL ---
    let a := fun j => (e j).re
    let a' := fun j => (e j).im
    ‖z‖ ^ 2 * (a ⬝ᵥ (P *ᵥ a) + a' ⬝ᵥ (P *ᵥ a')) + (1 + ε) * ∑ i, ‖e i‖ ^ 2 ≤
      (a ⬝ᵥ (P *ᵥ a) + a' ⬝ᵥ (P *ᵥ a')) +
        (γ ^ 2 - ε) * (∑ j, ‖dw j‖ ^ 2 + ∑ j, ‖dv j‖ ^ 2) := by -- --- PROOF ---
  intro a a'
  have hPT : Pᵀ = P := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hP.isHermitian.eq
  have hsym : ∀ u v : Vec ℝ n, u ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ u) := fun u v => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hPT, dotProduct_comm]
  -- the real and imaginary parts of the equation
  have hre := congrArg (fun x : Fin n → ℂ => fun i => (x i).re) h
  have him := congrArg (fun x : Fin n → ℂ => fun i => (x i).im) h
  simp only [Pi.sub_apply, Pi.add_apply, Complex.sub_re, Complex.add_re, Complex.sub_im,
    Complex.add_im, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im] at hre him
  have hq : z.re • a - z.im • a' = (A - P⁻¹ * Y * C) *ᵥ a + E *ᵥ (fun j => (dw j).re) -
      (P⁻¹ * Y * F) *ᵥ (fun j => (dv j).re) := by
    rw [← (aux_re_im_mulVec _ e).1, ← (aux_re_im_mulVec _ dw).1, ← (aux_re_im_mulVec _ dv).1]
    funext i
    simpa [a, a'] using congrFun hre i
  have hq' : z.re • a' + z.im • a = (A - P⁻¹ * Y * C) *ᵥ a' + E *ᵥ (fun j => (dw j).im) -
      (P⁻¹ * Y * F) *ᵥ (fun j => (dv j).im) := by
    rw [← (aux_re_im_mulVec _ e).2, ← (aux_re_im_mulVec _ dw).2, ← (aux_re_im_mulVec _ dv).2]
    funext i
    simpa [a, a'] using congrFun him i
  have h1 := hd a (fun j => (dw j).re) (fun j => (dv j).re)
  have h2 := hd a' (fun j => (dw j).im) (fun j => (dv j).im)
  simp only at h1 h2
  rw [← hq] at h1
  rw [← hq'] at h2
  -- `|z|² (aᵀPa + a'ᵀPa')` is the sum of the two `qᵀPq`, `P` symmetric
  have hz : (z.re • a - z.im • a') ⬝ᵥ (P *ᵥ (z.re • a - z.im • a')) +
      (z.re • a' + z.im • a) ⬝ᵥ (P *ᵥ (z.re • a' + z.im • a)) =
        ‖z‖ ^ 2 * (a ⬝ᵥ (P *ᵥ a) + a' ⬝ᵥ (P *ᵥ a')) := by
    have hs := hsym a a'
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [mulVec_sub, mulVec_add, mulVec_smul, dotProduct_sub, dotProduct_add,
      sub_dotProduct, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [hs]
    ring
  rw [aux_sum_sq_norm e, aux_sum_sq_norm dw, aux_sum_sq_norm dv]
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.hinf_of_lmi (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ n nw)
    (F : Mat ℝ ny nv) (P : Mat ℝ n n) (Y : Mat ℝ n ny) (γ : ℝ) (hγ : 0 < γ) (hP : P.PosDef)
    (h : LinearSysDT.HinfLmi A C E F P Y γ) : -- --- CONCL ---
    let Ae := (A - P⁻¹ * Y * C).map Complex.ofReal
    let Ec := E.map Complex.ofReal
    let Gc := (P⁻¹ * Y * F).map Complex.ofReal
    (∀ (μ : ℂ) (e : Fin n → ℂ), e ≠ 0 → Ae *ᵥ e = μ • e → ‖μ‖ < 1) ∧
      ∃ γ' < γ, ∀ z : ℂ, ‖z‖ = 1 → ∀ (e : Fin n → ℂ) (dw : Fin nw → ℂ) (dv : Fin nv → ℂ),
        z • e = Ae *ᵥ e + Ec *ᵥ dw - Gc *ᵥ dv →
          ∑ i, ‖e i‖ ^ 2 ≤ γ' ^ 2 * (∑ j, ‖dw j‖ ^ 2 + ∑ j, ‖dv j‖ ^ 2) := by -- --- PROOF ---
  intro Ae Ec Gc
  obtain ⟨ε, hε, hd⟩ := LinearSysDT.dissipation_of_hinfLmi A C E F P Y γ hP h
  -- `aᵀPa + a'ᵀPa' ≥ 0`, `P ≻ 0`
  have hPpos : ∀ x : Vec ℝ n, 0 ≤ x ⬝ᵥ (P *ᵥ x) := fun x => by
    have := (posSemidef_iff_dotProduct_mulVec.mp hP.posSemidef).2 x
    simpa using this
  have hnorm : ∀ {k : ℕ} (x : Fin k → ℂ), 0 ≤ ∑ i, ‖x i‖ ^ 2 :=
    fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  refine ⟨fun μ e he hμ => ?_, ?_⟩
  · -- stability: an eigenvector with `d = 0`
    have hc := LinearSysDT.aux_complex_dissipation A C E F P Y γ ε hP hd μ e 0 0
      (by rw [← hμ]; simp [Ae])
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, add_zero, mul_zero] at hc
    have hN : 0 < ∑ i, ‖e i‖ ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp he
      exact lt_of_lt_of_le (by positivity : 0 < ‖e i‖ ^ 2)
        (Finset.single_le_sum (fun j _ => sq_nonneg ‖e j‖) (Finset.mem_univ i))
    have hQ := add_nonneg (hPpos fun j => (e j).re) (hPpos fun j => (e j).im)
    by_contra hge
    push Not at hge
    have h1 : 1 ≤ ‖μ‖ ^ 2 := one_le_pow₀ hge
    nlinarith
  · -- the `H∞` bound on the unit circle
    refine ⟨Real.sqrt (max (γ ^ 2 - ε) 0), ?_, fun z hz e dw dv hzed => ?_⟩
    · calc Real.sqrt (max (γ ^ 2 - ε) 0) < Real.sqrt (γ ^ 2) :=
            Real.sqrt_lt_sqrt (le_max_right _ _) (max_lt (by linarith) (by positivity))
        _ = γ := Real.sqrt_sq hγ.le
    have hc := LinearSysDT.aux_complex_dissipation A C E F P Y γ ε hP hd z e dw dv hzed
    simp only [hz, one_pow, one_mul] at hc
    rw [Real.sq_sqrt (le_max_right _ _)]
    have hD := add_nonneg (hnorm dw) (hnorm dv)
    have hm : (γ ^ 2 - ε) * (∑ j, ‖dw j‖ ^ 2 + ∑ j, ‖dv j‖ ^ 2) ≤
        max (γ ^ 2 - ε) 0 * (∑ j, ‖dw j‖ ^ 2 + ∑ j, ‖dv j‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hD
    have hm0 : 0 ≤ max (γ ^ 2 - ε) 0 * (∑ j, ‖dw j‖ ^ 2 + ∑ j, ‖dv j‖ ^ 2) :=
      mul_nonneg (le_max_right _ _) hD
    nlinarith [hnorm e]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
