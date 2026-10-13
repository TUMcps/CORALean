import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiBasis
import CORALean.ContDynamics.LinearSys.Krylov.Operations.ArnoldiHessenberg
import CORALean.ContDynamics.LinearSys.Krylov.Operations.Augment
import CORALean.ContDynamics.LinearSys.Operations.InputReach
import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormFlow
import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The varying-input enclosure fails with Prop. B.1's error bound

[1, Thm. IV.2] encloses `R_p(δ)` by Krylov terms `P Ṽ(u) M e₁` and the box
`[-1, 1]ⁿ{ε̃(u) | u ∈ U}δ`, `ε̃(u) = h_{ξ+1,ξ} ω ϕ` from [1, Prop. B.1]. Take the skew
`A = [0 -40 -1 0; 40 0 0 -1; 1 0 0 -40; 0 1 40 0]`, two oscillators of frequency `40` coupled at
frequency `1`: `e^{τA}e₁ = (cos τ cos 40τ, cos τ sin 40τ, sin τ cos 40τ, sin τ sin 40τ)`. With
`U = [-1, 1](1/10, 0, 0, 0)`, `δ = π`, `ξ = 3`, Alg. 1 on `[A u; 0 0]`, `[0₄; 1]` spans
`e₅, e₁, (0, 40, 1, 0, 0)`, so every Krylov term has fourth coordinate `0`. `h₄,₃ = 80/√1601` is
small, `e₃ᵀe^{H̃t}e₁ = |u₁|(1 - cos(√1601 t))/√1601` oscillates below `2|u₁|/√1601`, and
`ν ≤ |u₁|/2` as `A` is skew: `ε̃(u) ≤ 1/50`. The input `-sin s sin 40s · (1/10, 0, 0, 0)` makes
the fourth coordinate of the integrand `(sin s sin 40s)²/10` and reaches `y₄ = π/40 > π/50`. A
constant input averages the oscillation out, a varying one rectifies it; `ε̃` sees only the
former. At `u = 0`, `h₄,₃ = 0`, so with `U = (0₄, w)` [1, Cor. IV.2] fails at the same point.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace MeasureTheory intervalIntegral

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A solution of `ḟ = M f` is `e^{tM} f(0)`. -/
theorem Krylov.aux_exp_mulVec_eq_of_hasDerivAt {m : ℕ} (M : Mat ℝ m m) (f : ℝ → Vec ℝ m)
    (hf : ∀ t, HasDerivAt f (M *ᵥ f t) t) (t : ℝ) :
    exp (t • M) *ᵥ f 0 = f t := by -- --- PROOF ---
  -- `e^{-sM} f(s)` has derivative `0`
  have hg : ∀ s, HasDerivAt (fun s => exp (s • (-M)) *ᵥ f s) 0 s := by
    intro s
    have hC : HasDerivAt (fun r => mulVecL (exp (r • (-M)))) (mulVecL ((-M) * exp (s • (-M))))
        s :=
      (ContinuousLinearMap.hasFDerivAt mulVecL).comp_hasDerivAt s
        (hasDerivAt_exp_smul_const' (-M) s)
    have h3 : HasDerivAt (fun s => exp (s • (-M)) *ᵥ f s)
        (((-M) * exp (s • (-M))) *ᵥ f s + exp (s • (-M)) *ᵥ (M *ᵥ f s)) s := hC.clm_apply (hf s)
    refine h3.congr_deriv ?_
    have hc : Commute (-M) (exp (s • (-M))) := ((Commute.refl (-M)).smul_right s).exp_right
    rw [Matrix.mulVec_mulVec, show (-M) * exp (s • (-M)) = exp (s • (-M)) * (-M) from hc.eq,
      Matrix.mul_neg, Matrix.neg_mulVec, neg_add_cancel]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt)
    (fun s => (hg s).deriv) t 0
  simp only [zero_smul, exp_zero, one_mulVec] at hconst
  -- so `f(t) = e^{tM} e^{-tM} f(t) = e^{tM} f(0)`
  rw [← hconst, Matrix.mulVec_mulVec, smul_neg, ← neg_smul]
  have hc : Commute (t • M) ((-t) • M) := ((Commute.refl M).smul_left t).smul_right (-t)
  have hmul : exp (t • M) * exp ((-t) • M) = 1 := by
    have h := (exp_add_of_commute hc).symm
    rw [← add_smul, add_neg_cancel, zero_smul, exp_zero] at h
    exact h
  rw [hmul, one_mulVec]

/-- `e^{τA}w` for the coupled oscillators, `w = (1/10, 0, 0, 0)`. -/
theorem Krylov.aux_exp_rot_mulVec (τ : ℝ) :
    exp (τ • !![(0 : ℝ), -40, -1, 0; 40, 0, 0, -1; 1, 0, 0, -40; 0, 1, 40, 0])
        *ᵥ ![1 / 10, 0, 0, 0]
      = ![Real.cos τ * Real.cos (40 * τ) / 10, Real.cos τ * Real.sin (40 * τ) / 10,
          Real.sin τ * Real.cos (40 * τ) / 10,
          Real.sin τ * Real.sin (40 * τ) / 10] := by -- --- PROOF ---
  set f : ℝ → Vec ℝ 4 := fun τ => ![Real.cos τ * Real.cos (40 * τ) / 10,
    Real.cos τ * Real.sin (40 * τ) / 10, Real.sin τ * Real.cos (40 * τ) / 10,
    Real.sin τ * Real.sin (40 * τ) / 10] with hf
  have h0 : f 0 = ![1 / 10, 0, 0, 0] := by
    ext i
    fin_cases i <;> simp [hf]
  rw [← h0]
  refine Krylov.aux_exp_mulVec_eq_of_hasDerivAt _ f (fun t => ?_) τ
  have hs := Real.hasDerivAt_sin t
  have hc := Real.hasDerivAt_cos t
  have hl : HasDerivAt (fun x : ℝ => 40 * x) 40 t := by
    simpa using (hasDerivAt_id t).const_mul (40 : ℝ)
  have hS := (Real.hasDerivAt_sin (40 * t)).comp t hl
  have hC := (Real.hasDerivAt_cos (40 * t)).comp t hl
  -- coordinate by coordinate, the product rule gives `A f`
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · refine ((hc.mul hC).div_const 10).congr_deriv ?_
    simp [mulVec, dotProduct, Fin.sum_univ_four, hf]
    ring
  · refine ((hc.mul hS).div_const 10).congr_deriv ?_
    simp [mulVec, dotProduct, Fin.sum_univ_four, hf]
    ring
  · refine ((hs.mul hC).div_const 10).congr_deriv ?_
    simp [mulVec, dotProduct, Fin.sum_univ_four, hf]
    ring
  · refine ((hs.mul hS).div_const 10).congr_deriv ?_
    simp [mulVec, dotProduct, Fin.sum_univ_four, hf]
    ring

/-- `e^{tH}e₁ = (1, a sin(rt)/r, a(1 - cos(rt))/r)` for `H = [0 0 0; a 0 -r; 0 r 0]`. -/
theorem Krylov.aux_exp_hess_mulVec (a r t : ℝ) (hr : r ≠ 0) :
    exp (t • !![(0 : ℝ), 0, 0; a, 0, -r; 0, r, 0]) *ᵥ ![1, 0, 0]
      = ![1, a * Real.sin (r * t) / r, a * (1 - Real.cos (r * t)) / r] := by -- --- PROOF ---
  set f : ℝ → Vec ℝ 3 := fun t => ![1, a * Real.sin (r * t) / r,
    a * (1 - Real.cos (r * t)) / r] with hf
  have h0 : f 0 = ![1, 0, 0] := by
    ext i
    fin_cases i <;> simp [hf]
  rw [← h0]
  refine Krylov.aux_exp_mulVec_eq_of_hasDerivAt _ f (fun t => ?_) t
  have hl : HasDerivAt (fun x : ℝ => r * x) r t := by
    simpa using (hasDerivAt_id t).const_mul r
  have hS := (Real.hasDerivAt_sin (r * t)).comp t hl
  have hC := (Real.hasDerivAt_cos (r * t)).comp t hl
  -- coordinate by coordinate, `ḟ = H f`
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · refine (hasDerivAt_const t (1 : ℝ)).congr_deriv ?_
    simp [mulVec, dotProduct, Fin.sum_univ_three, hf]
  · refine ((hS.const_mul a).div_const r).congr_deriv ?_
    simp [mulVec, dotProduct, Fin.sum_univ_three, hf]
    field_simp
    ring
  · refine (((hC.const_sub 1).const_mul a).div_const r).congr_deriv ?_
    simp [mulVec, dotProduct, Fin.sum_univ_three, hf]
    field_simp

/-- `∫₀^π cos(2ks) ds = 0` for `k ≠ 0`. -/
theorem Krylov.aux_integral_cos_two_mul (k : ℕ) (hk : k ≠ 0) :
    ∫ s in (0 : ℝ)..Real.pi, Real.cos (2 * k * s) = 0 := by -- --- PROOF ---
  have hk' : (2 * k : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk', integral_cos]
  simp only [mul_zero, Real.sin_zero, sub_zero]
  rw [show (2 * k : ℝ) * Real.pi = ((2 * k : ℕ) : ℝ) * Real.pi by push_cast; ring,
    Real.sin_nat_mul_pi, smul_zero]

/-- `∫₀^π (sin s sin 40s)² ds = π/4`. -/
theorem Krylov.aux_integral_sin_mul_sin_sq :
    ∫ s in (0 : ℝ)..Real.pi, (Real.sin s * Real.sin (40 * s)) ^ 2
      = Real.pi / 4 := by -- --- PROOF ---
  -- `(sin s sin 40s)² = 1/4 - cos 2s/4 - cos 80s/4 + cos 78s/8 + cos 82s/8`
  have hid : ∀ s : ℝ, (Real.sin s * Real.sin (40 * s)) ^ 2
      = 1 / 4 - Real.cos (2 * (1 : ℕ) * s) / 4 - Real.cos (2 * (40 : ℕ) * s) / 4
        + Real.cos (2 * (39 : ℕ) * s) / 8 + Real.cos (2 * (41 : ℕ) * s) / 8 := by
    intro s
    push_cast
    have h1 : Real.cos (2 * 39 * s) = Real.cos (80 * s - 2 * s) := by ring_nf
    have h2 : Real.cos (2 * 41 * s) = Real.cos (80 * s + 2 * s) := by ring_nf
    rw [h1, h2, Real.cos_sub, Real.cos_add, show (2 : ℝ) * 40 * s = 2 * (40 * s) by ring,
      show (80 : ℝ) * s = 2 * (40 * s) by ring, show (2 : ℝ) * 1 * s = 2 * s by ring,
      Real.cos_two_mul, Real.cos_two_mul (40 * s), Real.cos_sq', Real.cos_sq' (40 * s)]
    ring
  simp_rw [hid]
  -- every cosine integrates to `0` over whole periods
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_sub, intervalIntegral.integral_sub, intervalIntegral.integral_div,
    intervalIntegral.integral_div, intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_div, Krylov.aux_integral_cos_two_mul 1 one_ne_zero,
    Krylov.aux_integral_cos_two_mul 40 (by norm_num), Krylov.aux_integral_cos_two_mul 39
      (by norm_num), Krylov.aux_integral_cos_two_mul 41 (by norm_num)]
  · simp
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The augmented matrix of the coupled oscillators and `u = (a, 0, 0, 0)`, applied. -/
theorem Krylov.aux_augment_rot_mulVec (a : ℝ) (x : Fin 5 → ℝ) :
    Krylov.augment !![(0 : ℝ), -40, -1, 0; 40, 0, 0, -1; 1, 0, 0, -40; 0, 1, 40, 0]
        ![a, 0, 0, 0] *ᵥ x
      = ![-40 * x 1 - x 2 + a * x 4, 40 * x 0 - x 3, x 0 - 40 * x 3, x 1 + 40 * x 2,
          0] := by -- --- PROOF ---
  have hC : Krylov.augment !![(0 : ℝ), -40, -1, 0; 40, 0, 0, -1; 1, 0, 0, -40; 0, 1, 40, 0]
      ![a, 0, 0, 0] = !![0, -40, -1, 0, a; 40, 0, 0, -1, 0; 1, 0, 0, -40, 0;
        0, 1, 40, 0, 0; 0, 0, 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hC]
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_five] <;> ring

/-- A pass keeps the vectors stored before it. -/
theorem Krylov.aux_arnoldi_fst_stable {n : ℕ} (C : Mat ℝ n n) (v : Vec ℝ n) {p q i : ℕ}
    (hpq : p ≤ q) (hi : i ≤ p) :
    (Krylov.arnoldi C v q).1 i = (Krylov.arnoldi C v p).1 i := by -- --- PROOF ---
  induction q, hpq using Nat.le_induction with
  | base => rfl
  | succ q hpq ih =>
    rw [← ih, Krylov.arnoldi.eq_2]
    exact Function.update_of_ne (by omega) _ _

/-- A pass keeps the Hessenberg columns stored before it. -/
theorem Krylov.aux_arnoldi_snd_stable {n : ℕ} (C : Mat ℝ n n) (v : Vec ℝ n) {p q k : ℕ}
    (hpq : p ≤ q) (hk : k < p) (i : ℕ) :
    (Krylov.arnoldi C v q).2 i k = (Krylov.arnoldi C v p).2 i k := by -- --- PROOF ---
  induction q, hpq using Nat.le_induction with
  | base => rfl
  | succ q hpq ih =>
    rw [← ih, Krylov.arnoldi.eq_2]
    exact if_neg (by omega)

/-- Pass `k + 1` of Alg. 1 stores `v⁽ᵏ⁺²⁾ = w/‖w‖`, `w` the swept `C v⁽ᵏ⁺¹⁾`. -/
theorem Krylov.aux_arnoldi_succ_fst {n : ℕ} (C : Mat ℝ n n) (v : Vec ℝ n) (k : ℕ) :
    (Krylov.arnoldi C v (k + 1)).1 (k + 1)
      = ‖(Krylov.gramSchmidtStep (C *ᵥ (Krylov.arnoldi C v k).1 k) (Krylov.arnoldi C v k).1
          (k + 1)).1‖₂⁻¹ • (Krylov.gramSchmidtStep (C *ᵥ (Krylov.arnoldi C v k).1 k)
          (Krylov.arnoldi C v k).1 (k + 1)).1 := by
  rw [Krylov.arnoldi.eq_2]
  exact Function.update_self ..

/-- Pass `k + 1` of Alg. 1 stores the column `k` of `H`. -/
theorem Krylov.aux_arnoldi_succ_snd {n : ℕ} (C : Mat ℝ n n) (v : Vec ℝ n) (k i : ℕ) :
    (Krylov.arnoldi C v (k + 1)).2 i k
      = if i ≤ k then (Krylov.gramSchmidtStep (C *ᵥ (Krylov.arnoldi C v k).1 k)
          (Krylov.arnoldi C v k).1 (k + 1)).2 i
        else if i = k + 1 then ‖(Krylov.gramSchmidtStep (C *ᵥ (Krylov.arnoldi C v k).1 k)
          (Krylov.arnoldi C v k).1 (k + 1)).1‖₂ else 0 := by
  rw [Krylov.arnoldi.eq_2]
  simp

/-- `‖x‖₂` in five coordinates. -/
theorem Krylov.aux_norm₂_five (x : Fin 5 → ℝ) :
    ‖x‖₂ = √(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2) := by
  simp [norm₂, Fin.sum_univ_five]

/-- Alg. 1 starts from `v⁽¹⁾ = ṽ = e₅`. -/
theorem Krylov.aux_rot_vec0 (C : Mat ℝ 5 5) (i : ℕ) :
    (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 0).1 i = ![0, 0, 0, 0, 1] := by -- --- PROOF ---
  have hv : (Pi.single (Fin.last 4) 1 : Fin 5 → ℝ) = ![0, 0, 0, 0, 1] := by
    ext j
    fin_cases j <;> rfl
  rw [Krylov.arnoldi.eq_1]
  dsimp only
  rw [hv, show ‖(![0, 0, 0, 0, 1] : Fin 5 → ℝ)‖₂ = 1 by simp [Krylov.aux_norm₂_five], inv_one,
    one_smul]

/-- The first sweep: `C̃e₅ = (a, 0, 0, 0, 0)`, orthogonal to `e₅`. -/
theorem Krylov.aux_rot_sweep1 (a : ℝ) (C : Mat ℝ 5 5)
    (hC : ∀ x, C *ᵥ x
      = ![-40 * x 1 - x 2 + a * x 4, 40 * x 0 - x 3, x 0 - 40 * x 3, x 1 + 40 * x 2, 0]) :
    Krylov.gramSchmidtStep (C *ᵥ (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 0).1 0)
        (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 0).1 1
      = (![a, 0, 0, 0, 0], fun _ => 0) := by -- --- PROOF ---
  simp only [Krylov.gramSchmidtStep, Krylov.aux_rot_vec0, hC]
  refine Prod.ext ?_ ?_
  · ext i
    fin_cases i <;> simp [dotProduct, Fin.sum_univ_five]
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> simp [dotProduct, Fin.sum_univ_five]

/-- After the first pass: `v⁽¹⁾ = e₅`, `v⁽²⁾ = σe₁`, `σ = a/|a|`. -/
theorem Krylov.aux_rot_vec1 (a : ℝ) (C : Mat ℝ 5 5)
    (hC : ∀ x, C *ᵥ x
      = ![-40 * x 1 - x 2 + a * x 4, 40 * x 0 - x 3, x 0 - 40 * x 3, x 1 + 40 * x 2, 0])
    (i : ℕ) (hi : i ≤ 1) :
    (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 1).1 i
      = if i = 0 then ![0, 0, 0, 0, 1] else ![a / |a|, 0, 0, 0, 0] := by -- --- PROOF ---
  interval_cases i
  · rw [Krylov.aux_arnoldi_fst_stable C _ (Nat.zero_le 1) le_rfl, Krylov.aux_rot_vec0]
    rfl
  · rw [Krylov.aux_arnoldi_succ_fst, Krylov.aux_rot_sweep1 a C hC]
    have hn1 : ‖(![a, 0, 0, 0, 0] : Fin 5 → ℝ)‖₂ = |a| := by
      simp [Krylov.aux_norm₂_five, Real.sqrt_sq_eq_abs]
    rw [hn1]
    ext j
    fin_cases j <;> simp [div_eq_inv_mul]

/-- The second sweep: `C̃σe₁ = σ(0, 40, 1, 0, 0)`, orthogonal to `e₅` and `e₁`. -/
theorem Krylov.aux_rot_sweep2 (a σ : ℝ) (C : Mat ℝ 5 5)
    (hC : ∀ x, C *ᵥ x
      = ![-40 * x 1 - x 2 + a * x 4, 40 * x 0 - x 3, x 0 - 40 * x 3, x 1 + 40 * x 2, 0])
    (hV : ∀ i ≤ 1, (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 1).1 i
      = if i = 0 then ![0, 0, 0, 0, 1] else ![σ, 0, 0, 0, 0]) :
    Krylov.gramSchmidtStep (C *ᵥ (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 1).1 1)
        (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 1).1 2
      = (![0, 40 * σ, σ, 0, 0], fun _ => 0) := by -- --- PROOF ---
  simp only [Krylov.gramSchmidtStep, hV 0 (by norm_num), hV 1 le_rfl, hC]
  refine Prod.ext ?_ ?_
  · ext i
    fin_cases i <;> simp [dotProduct, Fin.sum_univ_five]
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> simp [dotProduct, Fin.sum_univ_five]

/-- After the second pass: `v⁽³⁾ = σ(0, 40, 1, 0, 0)/√1601`. -/
theorem Krylov.aux_rot_vec2 (a σ : ℝ) (hσ2 : σ * σ = 1) (C : Mat ℝ 5 5)
    (hC : ∀ x, C *ᵥ x
      = ![-40 * x 1 - x 2 + a * x 4, 40 * x 0 - x 3, x 0 - 40 * x 3, x 1 + 40 * x 2, 0])
    (hV : ∀ i ≤ 1, (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 1).1 i
      = if i = 0 then ![0, 0, 0, 0, 1] else ![σ, 0, 0, 0, 0]) (i : ℕ) (hi : i ≤ 2) :
    (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 2).1 i = if i = 0 then ![0, 0, 0, 0, 1]
      else if i = 1 then ![σ, 0, 0, 0, 0]
      else ![0, 40 * σ / √1601, σ / √1601, 0, 0] := by -- --- PROOF ---
  interval_cases i
  · rw [Krylov.aux_arnoldi_fst_stable C _ (Nat.zero_le 2) le_rfl, Krylov.aux_rot_vec0]
    rfl
  · rw [Krylov.aux_arnoldi_fst_stable C _ (by norm_num : 1 ≤ 2) le_rfl, hV 1 le_rfl]
    rfl
  · rw [Krylov.aux_arnoldi_succ_fst, Krylov.aux_rot_sweep2 a σ C hC hV]
    have hn2 : ‖(![0, 40 * σ, σ, 0, 0] : Fin 5 → ℝ)‖₂ = √1601 := by
      rw [Krylov.aux_norm₂_five]
      congr 1
      simp
      linear_combination 1601 * hσ2
    rw [hn2]
    have hr0 : 0 < √1601 := by positivity
    ext j
    fin_cases j <;> simp <;> field_simp

/-- The third sweep: `C̃v⁽³⁾ + √1601 v⁽²⁾ = (0, 0, 0, 80σ/√1601, 0)`, `h₂,₃ = -√1601`. -/
theorem Krylov.aux_rot_sweep3 (a σ : ℝ) (hσ2 : σ * σ = 1) (C : Mat ℝ 5 5)
    (hC : ∀ x, C *ᵥ x
      = ![-40 * x 1 - x 2 + a * x 4, 40 * x 0 - x 3, x 0 - 40 * x 3, x 1 + 40 * x 2, 0])
    (hV : ∀ i ≤ 2, (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 2).1 i
      = if i = 0 then ![0, 0, 0, 0, 1] else if i = 1 then ![σ, 0, 0, 0, 0]
        else ![0, 40 * σ / √1601, σ / √1601, 0, 0]) :
    Krylov.gramSchmidtStep (C *ᵥ (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 2).1 2)
        (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 2).1 3
      = (![0, 0, 0, 80 * σ / √1601, 0],
          fun i => if i = 1 then -√1601 else 0) := by -- --- PROOF ---
  have hr : √1601 * √1601 = 1601 := Real.mul_self_sqrt (by norm_num)
  have hr0 : 0 < √1601 := by positivity
  simp only [Krylov.gramSchmidtStep, hV 0 (by norm_num), hV 1 (by norm_num), hV 2 le_rfl, hC]
  refine Prod.ext ?_ ?_
  · ext i
    fin_cases i <;> simp [dotProduct, Fin.sum_univ_five] <;> field_simp <;>
      first | ring1 | linear_combination (1601 * σ) * hσ2
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> (try omega) <;> (try contradiction) <;>
      simp [dotProduct, Fin.sum_univ_five]
    field_simp
    linear_combination (-1601) * hσ2 + hr

/-- Alg. 1 at `ξ = 3`, `u = (a, 0, 0, 0)`, `a ≠ 0`: fourth row of the basis `0`,
`H = [0 0 0; |a| 0 -√1601; 0 √1601 0]`, `h₄,₃ = 80/√1601`. -/
theorem Krylov.aux_arnoldi_rot (a : ℝ) (ha : a ≠ 0) (C : Mat ℝ 5 5)
    (hC : ∀ x, C *ᵥ x
      = ![-40 * x 1 - x 2 + a * x 4, 40 * x 0 - x 3, x 0 - 40 * x 3, x 1 + 40 * x 2, 0]) :
    (∀ k : Fin 3, Krylov.arnoldiBasis C (Pi.single (Fin.last 4) 1) 3 (Fin.castSucc 3) k = 0)
      ∧ (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 3).2 3 2 = 80 / √1601
      ∧ Krylov.arnoldiHessenberg C (Pi.single (Fin.last 4) 1) 3
          = !![0, 0, 0; |a|, 0, -√1601; 0, √1601, 0] := by -- --- PROOF ---
  have hσ2 : a / |a| * (a / |a|) = 1 := by
    rw [div_mul_div_comm, ← sq, ← sq, sq_abs, div_self (pow_ne_zero 2 ha)]
  have hV1 := Krylov.aux_rot_vec1 a C hC
  have hV2 := Krylov.aux_rot_vec2 a _ hσ2 C hC hV1
  have hs1 := Krylov.aux_rot_sweep1 a C hC
  have hs2 := Krylov.aux_rot_sweep2 a _ C hC hV1
  have hs3 := Krylov.aux_rot_sweep3 a _ hσ2 C hC hV2
  have hr0 : 0 < √1601 := by positivity
  -- the norms of the three swept vectors
  have hn1 : ‖(![a, 0, 0, 0, 0] : Fin 5 → ℝ)‖₂ = |a| := by
    simp [Krylov.aux_norm₂_five, Real.sqrt_sq_eq_abs]
  have hn2 : ‖(![0, 40 * (a / |a|), a / |a|, 0, 0] : Fin 5 → ℝ)‖₂ = √1601 := by
    rw [Krylov.aux_norm₂_five]
    congr 1
    simp
    linear_combination 1601 * hσ2
  have hn3 : ‖(![0, 0, 0, 80 * (a / |a|) / √1601, 0] : Fin 5 → ℝ)‖₂ = 80 / √1601 := by
    rw [Krylov.aux_norm₂_five]
    simp only [Matrix.cons_val, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_add, add_zero]
    rw [show (80 * (a / |a|) / √1601) ^ 2 = (80 / √1601) ^ 2 by
      rw [div_pow, div_pow, mul_pow, sq (a / |a|), hσ2, mul_one], Real.sqrt_sq (by positivity)]
  -- column `k` of `H` is stored by pass `k + 1`
  have hcol : ∀ i k : ℕ, k < 3 → (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 3).2 i k
      = (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) (k + 1)).2 i k :=
    fun i k hk => Krylov.aux_arnoldi_snd_stable C _ (by omega : k + 1 ≤ 3) (by omega) i
  refine ⟨fun k => ?_, ?_, ?_⟩
  · show (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 3).1 k 3 = 0
    rw [Krylov.aux_arnoldi_fst_stable C _ (by omega : 2 ≤ 3) (by omega : (k : ℕ) ≤ 2),
      hV2 k (by omega)]
    fin_cases k <;> rfl
  · rw [hcol 3 2 (by norm_num), Krylov.aux_arnoldi_succ_snd, hs3, if_neg (by norm_num),
      if_pos rfl, hn3]
  · -- `H` entry by entry, column `k` from pass `k + 1`
    ext i k
    show (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 3).2 i k = _
    rw [hcol i k k.isLt, Krylov.aux_arnoldi_succ_snd]
    simp only [show (Fin.last 4 : Fin 5) = 4 from rfl] at hs1 hs2 hs3
    fin_cases i <;> fin_cases k <;>
      simp [hs1, hs2, hs3, hn1, hn2]

/-- Alg. 1 at `ξ = 3` with `u = 0`: the vectors after `e₅` and `h₄,₃` are `0`. -/
theorem Krylov.aux_arnoldi_rot_zero (C : Mat ℝ 5 5)
    (hC : ∀ x, C *ᵥ x
      = ![-40 * x 1 - x 2 + 0 * x 4, 40 * x 0 - x 3, x 0 - 40 * x 3, x 1 + 40 * x 2, 0]) :
    (∀ k : Fin 3, Krylov.arnoldiBasis C (Pi.single (Fin.last 4) 1) 3 (Fin.castSucc 3) k = 0)
      ∧ (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 3).2 3 2 = 0 := by -- --- PROOF ---
  have h0 : ∀ V : ℕ → Fin 5 → ℝ, ∀ j, (Krylov.gramSchmidtStep 0 V j).1 = 0 := by
    intro V j
    induction j with
    | zero => rfl
    | succ j ih => simp [Krylov.gramSchmidtStep, ih]
  have hCe : C *ᵥ ![0, 0, 0, 0, 1] = 0 := by
    rw [hC]
    ext i
    fin_cases i <;> simp
  have hC0 : C *ᵥ 0 = 0 := Matrix.mulVec_zero C
  -- `C̃e₅ = 0`, so every later vector is `0`
  have hV1 : (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 1).1 1 = 0 := by
    rw [Krylov.aux_arnoldi_succ_fst, Krylov.aux_rot_vec0, hCe, h0, smul_zero]
  have hV2 : (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 2).1 2 = 0 := by
    rw [Krylov.aux_arnoldi_succ_fst, hV1, hC0, h0, smul_zero]
  refine ⟨fun k => ?_, ?_⟩
  · show (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 3).1 k 3 = 0
    fin_cases k
    · rw [Krylov.aux_arnoldi_fst_stable C _ (Nat.zero_le 3) le_rfl, Krylov.aux_rot_vec0]
      rfl
    · rw [Krylov.aux_arnoldi_fst_stable C _ (by norm_num : 1 ≤ 3) le_rfl, hV1]
      rfl
    · rw [Krylov.aux_arnoldi_fst_stable C _ (by norm_num : 2 ≤ 3) le_rfl, hV2]
      rfl
  · rw [Krylov.aux_arnoldi_succ_snd, if_neg (by norm_num), if_pos rfl, hV2, hC0, h0]
    simp [norm₂]

/-- `ν ≤ 1/20` for `ν = xᵀC̃x/‖x‖₂²`, `u = (a, 0, 0, 0)`, `|a| ≤ 1/10`: `xᵀC̃x = a x₁x₅`. -/
theorem Krylov.aux_rot_nu_le {a ν : ℝ} (ha : |a| ≤ 1 / 10) {x : Fin 5 → ℝ} (hx0 : x ≠ 0)
    (hx : x ⬝ᵥ (Krylov.augment !![(0 : ℝ), -40, -1, 0; 40, 0, 0, -1; 1, 0, 0, -40; 0, 1, 40, 0]
      ![a, 0, 0, 0] *ᵥ x) = ν * ‖x‖₂ ^ 2) : ν ≤ 1 / 20 := by -- --- PROOF ---
  rw [Krylov.aux_augment_rot_mulVec] at hx
  simp only [dotProduct, Fin.sum_univ_five, Matrix.cons_val] at hx
  -- `xᵀC̃x = a x₁x₅`, the skew part cancelling
  have hq : x 0 * (-40 * x 1 - x 2 + a * x 4) + x 1 * (40 * x 0 - x 3) + x 2 * (x 0 - 40 * x 3)
      + x 3 * (x 1 + 40 * x 2) + x 4 * 0 = a * x 0 * x 4 := by ring
  rw [hq] at hx
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  have hpos : 0 < ‖x‖₂ ^ 2 := pow_pos ((abs_pos.2 hi).trans_le (abs_le_norm₂ x i)) 2
  have hsq : x 0 ^ 2 + x 4 ^ 2 ≤ ‖x‖₂ ^ 2 := by
    rw [norm₂_sq, Fin.sum_univ_five]
    nlinarith [sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  -- `a x₁x₅ ≤ |a|(x₁² + x₅²)/2`
  have hax : a * x 0 * x 4 ≤ 1 / 20 * (x 0 ^ 2 + x 4 ^ 2) := by
    have h1 : a * x 0 * x 4 ≤ |a| * |x 0 * x 4| := by
      rw [mul_assoc, ← abs_mul]
      exact le_abs_self _
    have h2 : |x 0 * x 4| ≤ (x 0 ^ 2 + x 4 ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|x 0| - |x 4|), sq_abs (x 0), sq_abs (x 4)]
    calc a * x 0 * x 4 ≤ |a| * |x 0 * x 4| := h1
      _ ≤ 1 / 10 * ((x 0 ^ 2 + x 4 ^ 2) / 2) := mul_le_mul ha h2 (abs_nonneg _) (by norm_num)
      _ = 1 / 20 * (x 0 ^ 2 + x 4 ^ 2) := by ring
  refine le_of_mul_le_mul_right ?_ hpos
  linarith

/-- `ϕ ≤ 5/4` at `δ = π` for `ν ≤ 1/20`, and `ϕ ≥ 0`. -/
theorem Krylov.aux_phi_le {ν : ℝ} (hν : ν ≤ 1 / 20) :
    0 ≤ (if 0 < ν then (Real.exp (ν * Real.pi) - 1) / (ν * Real.pi) else 1)
      ∧ (if 0 < ν then (Real.exp (ν * Real.pi) - 1) / (ν * Real.pi) else 1)
        ≤ 5 / 4 := by -- --- PROOF ---
  split_ifs with h
  · have hπ := Real.pi_le_four
    have hx0 : 0 < ν * Real.pi := mul_pos h Real.pi_pos
    have hx1 : ν * Real.pi ≤ 1 / 5 := by nlinarith
    have h1 := Real.add_one_le_exp (ν * Real.pi)
    -- `eˣ < 1/(1 - x)`, so `(eˣ - 1)/x < 1/(1 - x) ≤ 5/4`
    have he := Real.exp_bound_div_one_sub_of_interval' hx0 (by linarith)
    refine ⟨div_nonneg (by linarith) hx0.le, ?_⟩
    rw [div_le_iff₀ hx0]
    rw [lt_div_iff₀ (by linarith)] at he
    nlinarith
  · norm_num

/-- `ε̃(u) = h₄,₃ ω ϕ ≤ 1/50` for `u = (β/10, 0, 0, 0)`, `|β| ≤ 1`; the fourth row of `P Ṽ(u)`
is `0`. -/
theorem Krylov.aux_rot_errorBound_le {β : ℝ} (hβ : β ∈ Set.Icc (-1 : ℝ) 1) :
    let C := Krylov.augment !![(0 : ℝ), -40, -1, 0; 40, 0, 0, -1; 1, 0, 0, -40; 0, 1, 40, 0]
      ![β / 10, 0, 0, 0]
    (∀ k : Fin 3, Krylov.arnoldiBasis C (Pi.single (Fin.last 4) 1) 3 (Fin.castSucc 3) k = 0)
      ∧ ∀ ν ω : ℝ, (∃ x : Fin 5 → ℝ, x ≠ 0 ∧ x ⬝ᵥ (C *ᵥ x) = ν * ‖x‖₂ ^ 2) →
        (∃ t ∈ Set.Icc 0 Real.pi, ω = |(exp (t • Krylov.arnoldiHessenberg C
            (Pi.single (Fin.last 4) 1) 3) *ᵥ Pi.single 0 1) 2|) →
        (Krylov.arnoldi C (Pi.single (Fin.last 4) 1) 3).2 3 2 * ω
          * (if 0 < ν then (Real.exp (ν * Real.pi) - 1) / (ν * Real.pi) else 1)
          ≤ 1 / 50 := by -- --- PROOF ---
  intro C
  have hC := Krylov.aux_augment_rot_mulVec (β / 10)
  rcases eq_or_ne β 0 with hβ0 | hβ0
  · -- `u = 0`: `h₄,₃ = 0`
    subst hβ0
    have hC0 := Krylov.aux_arnoldi_rot_zero C (fun x => by rw [hC x]; simp)
    refine ⟨hC0.1, fun ν ω _ _ => ?_⟩
    rw [hC0.2]
    norm_num
  have ha1 : |β / 10| ≤ 1 / 10 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 10)]
    have := abs_le.mpr hβ
    linarith
  obtain ⟨hrow, hh, hH⟩ := Krylov.aux_arnoldi_rot (β / 10) (by positivity) C hC
  refine ⟨hrow, fun ν ω hνx hω => ?_⟩
  obtain ⟨x, hx0, hx⟩ := hνx
  obtain ⟨hϕ0, hϕ⟩ := Krylov.aux_phi_le (Krylov.aux_rot_nu_le ha1 hx0 hx)
  have hr0 : 0 < √1601 := by positivity
  -- `ω ≤ 2|a|/√1601 ≤ 1/(5√1601)`
  obtain ⟨t, -, rfl⟩ := hω
  rw [hH, show (Pi.single 0 1 : Fin 3 → ℝ) = ![1, 0, 0] by
    ext i
    fin_cases i <;> rfl, Krylov.aux_exp_hess_mulVec _ _ _ hr0.ne', hh]
  simp only [Matrix.cons_val]
  have hcos := Real.cos_le_one (√1601 * t)
  have hcos' := Real.neg_one_le_cos (√1601 * t)
  rw [abs_of_nonneg (div_nonneg (mul_nonneg (abs_nonneg _) (by linarith)) hr0.le)]
  -- `|a|(1 - cos) ≤ 2/10`
  have hp : |β / 10| * (1 - Real.cos (√1601 * t)) ≤ 1 / 5 := by
    nlinarith [abs_nonneg (β / 10)]
  have hω : |β / 10| * (1 - Real.cos (√1601 * t)) / √1601 ≤ 1 / (5 * √1601) := by
    rw [div_le_div_iff₀ hr0 (by positivity)]
    nlinarith
  calc 80 / √1601 * (|β / 10| * (1 - Real.cos (√1601 * t)) / √1601)
        * (if 0 < ν then (Real.exp (ν * Real.pi) - 1) / (ν * Real.pi) else 1)
      ≤ 80 / √1601 * (1 / (5 * √1601)) * (5 / 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hω (by positivity)) hϕ hϕ0 (by positivity)
    _ = 20 / 1601 := by
        field_simp
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
    _ ≤ 1 / 50 := by norm_num

/-- The input `-sin s sin 40s · w` reaches `y` with `y₄ = π/40`. -/
theorem Krylov.aux_rot_mem_inputReach :
    ∃ y ∈ (LinearSys.mk !![(0 : ℝ), -40, -1, 0; 40, 0, 0, -1; 1, 0, 0, -40; 0, 1, 40, 0] :
        LinearSys ℝ 4).inputReach (S := fun k => Set (Vec ℝ k))
        {u | ∃ β ∈ Set.Icc (-1 : ℝ) 1, u = β • ![1 / 10, 0, 0, 0]} Real.pi,
      y 3 = Real.pi / 40 := by -- --- PROOF ---
  set A : Mat ℝ 4 4 := !![(0 : ℝ), -40, -1, 0; 40, 0, 0, -1; 1, 0, 0, -40; 0, 1, 40, 0] with hA
  set w : Vec ℝ 4 := ![1 / 10, 0, 0, 0] with hw
  set U : Set (Vec ℝ 4) := {u | ∃ β ∈ Set.Icc (-1 : ℝ) 1, u = β • w} with hUdef
  let c : ℝ → ℝ := fun s => -(Real.sin s * Real.sin (40 * s))
  have hcc : Continuous c := by fun_prop
  have hU : ∀ s ∈ Set.Icc (0 : ℝ) Real.pi, c s • w ∈ U := fun s _ => by
    refine ⟨c s, ⟨?_, ?_⟩, rfl⟩ <;>
      nlinarith [Real.abs_sin_le_one s, Real.abs_sin_le_one (40 * s), abs_nonneg (Real.sin s),
        abs_nonneg (Real.sin (40 * s)), abs_mul (Real.sin s) (Real.sin (40 * s)),
        neg_abs_le (Real.sin s * Real.sin (40 * s)), le_abs_self (Real.sin s * Real.sin (40 * s))]
  have hmeas : AEStronglyMeasurable (fun s => c s • w) (volume.restrict (Set.Icc 0 Real.pi)) :=
    (hcc.smul continuous_const).aestronglyMeasurable
  -- `U` is bounded by `1` in the sup norm
  have hbdd : Bornology.IsBounded U := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun u hu => ?_⟩
    obtain ⟨β, hβ, rfl⟩ := hu
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    have hw1 : ‖w‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
      fin_cases i <;> norm_num [hw]
    have : ‖β‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      exact hβ
    nlinarith [norm_nonneg w, norm_nonneg β]
  refine ⟨_, ⟨fun s => c s • w, hU, hmeas, rfl⟩, ?_⟩
  have hint := intervalIntegrable_expSub_mulVec (A := A) (c := Real.pi) Real.pi_pos.le
    (S := fun k => Set (Vec ℝ k)) (U := U) hbdd hU hmeas
  -- the fourth coordinate, read through the coordinate projection
  have hproj := ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3) hint
  simp only [ContinuousLinearMap.proj_apply] at hproj
  show (∫ s in (0 : ℝ)..Real.pi, exp ((Real.pi - s) • A) *ᵥ (c s • w)) 3 = Real.pi / 40
  rw [← hproj]
  have hpt : ∀ s, (exp ((Real.pi - s) • A) *ᵥ (c s • w)) 3
      = (Real.sin s * Real.sin (40 * s)) ^ 2 / 10 := fun s => by
    rw [Matrix.mulVec_smul, Pi.smul_apply, hA, hw, Krylov.aux_exp_rot_mulVec]
    simp only [Matrix.cons_val, smul_eq_mul, c]
    rw [Real.sin_pi_sub, show (40 : ℝ) * (Real.pi - s) = ((20 : ℕ) : ℝ) * (2 * Real.pi) - 40 * s
      by push_cast; ring, Real.sin_nat_mul_two_pi_sub]
    ring
  simp only [hpt]
  rw [intervalIntegral.integral_div, Krylov.aux_integral_sin_mul_sin_sq]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. IV.2] and [1, Cor. IV.2] fail with [1, Prop. B.1]'s `ε̃` (`ν` any Rayleigh quotient
of `C̃`, `ω` any value of `|e₃ᵀe^{H̃t}e₁|` on `[0, δ]`): every Krylov term has fourth coordinate
`0`, `ε̃(u) ≤ 1/50`, `ε̃(0) = 0`, yet a point of `R_p(π)` has `|y₄| > π/50`. -/
theorem Krylov.varying_input_reach_counterexample :
    let A : Mat ℝ 4 4 := !![0, -40, -1, 0; 40, 0, 0, -1; 1, 0, 0, -40; 0, 1, 40, 0]
    let w : Vec ℝ 4 := ![1 / 10, 0, 0, 0]
    let U : Set (Vec ℝ 4) := {u | ∃ β ∈ Set.Icc (-1 : ℝ) 1, u = β • w}
    let v : Fin 5 → ℝ := Pi.single (Fin.last 4) 1
    let δ : ℝ := Real.pi
    let ε : ℝ := 1 / 50
    (Krylov.arnoldi (Krylov.augment A 0) v 3).2 3 2 = 0
    ∧ (∀ u ∈ U,
      (∀ k : Fin 3, Krylov.arnoldiBasis (Krylov.augment A u) v 3 (Fin.castSucc 3) k = 0)
      ∧ ∀ ν ω : ℝ,
        (∃ x : Fin 5 → ℝ, x ≠ 0 ∧ x ⬝ᵥ (Krylov.augment A u *ᵥ x) = ν * ‖x‖₂ ^ 2) →
        (∃ t ∈ Set.Icc 0 δ, ω = |(exp (t • Krylov.arnoldiHessenberg (Krylov.augment A u) v 3)
            *ᵥ Pi.single 0 1) 2|) →
        (Krylov.arnoldi (Krylov.augment A u) v 3).2 3 2 * ω
          * (if 0 < ν then (Real.exp (ν * δ) - 1) / (ν * δ) else 1) ≤ ε)
      ∧ ∃ y ∈ (LinearSys.mk A : LinearSys ℝ 4).inputReach (S := fun k => Set (Vec ℝ k)) U δ,
          ε * δ < |y 3| := by -- --- PROOF ---
  intro A w U v δ ε
  refine ⟨?_, fun u hu => ?_, ?_⟩
  · -- `u = 0`: Alg. 1 breaks down at once
    have h0 : (0 : Vec ℝ 4) = ![0, 0, 0, 0] := by
      ext i
      fin_cases i <;> rfl
    rw [h0]
    exact (Krylov.aux_arnoldi_rot_zero _ (fun x => by rw [Krylov.aux_augment_rot_mulVec])).2
  · obtain ⟨β, hβ, rfl⟩ := hu
    have hu : β • w = ![β / 10, 0, 0, 0] := by
      ext i
      fin_cases i <;> simp [w]
      ring
    rw [hu]
    exact Krylov.aux_rot_errorBound_le hβ
  · obtain ⟨y, hy, hy3⟩ := Krylov.aux_rot_mem_inputReach
    refine ⟨y, hy, ?_⟩
    rw [hy3, abs_of_pos (by positivity)]
    have := Real.pi_pos
    show 1 / 50 * Real.pi < Real.pi / 40
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
