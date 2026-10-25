module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# The integral of `|δ_m|` between two trapezoidal estimates, by its effective order

[1, Eq. 6.8]: for `f(t) = |δ_m(t)| > 0` on `(0, T]` with effective order `ρ(t) = f'(t)t/f(t)`
(6.7) bounded by `1 ≤ m̃ ≤ ρ(t) ≤ m - 1`: `t/m f(t) ≤ ∫₀ᵗf(s)ds ≤ t/(m̃+1) f(t) ≤ t/2 f(t)`.
Stated for any `f` continuous on `[0, T]`, differentiable on `(0, T)`, positive on `(0, T]`, and
real `m̃`. `ρ ≥ c` makes `f(s)s^{-c}` nondecreasing and `ρ ≤ c` nonincreasing on `(0, T]`, so
`f(t)(s/t)^{m-1} ≤ f(s) ≤ f(t)(s/t)^{m̃}` for `0 < s ≤ t`, which integrate to the bounds; [1]
argues through a mean value `ρ(t*)` instead.

## Inputs
* `f` – positive function
* `f'` – its derivative
* `T` – upper limit
* `m'` – lower effective order
* `m` – upper effective order
* `t` – time

## Hypotheses
* `hf` – function continuous on the interval
* `hd` – derivative is the function's derivative
* `hpos` – function positive
* `hm'` – lower effective order at least one
* `hρ` – effective order between the bounds
* `ht` – time within the interval

## Conclusion
* the integral lies between the stated multiples of the end value

## References

* [1] T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `d/ds [f(s)s^{-c}] = s^{-c-1}(f'(s)s - cf(s))` at `s > 0`. -/
theorem Krylov.aux_hasDerivAt_mul_rpow_neg {f : ℝ → ℝ} {d c s : ℝ} (hs : 0 < s)
    (hd : HasDerivAt f d s) : -- --- CONCL ---
    HasDerivAt (fun x => f x * x ^ (-c)) (s ^ (-c - 1) * (d * s - c * f s)) s := by -- --- PROOF ---
  have h := hd.mul (Real.hasDerivAt_rpow_const (p := -c) (Or.inl hs.ne'))
  refine h.congr_deriv ?_
  have hp : s ^ (-c) = s ^ (-c - 1) * s := by
    rw [← Real.rpow_add_one hs.ne']
    ring_nf
  rw [hp]
  ring

/-- Between `0 < s ≤ t ≤ T`, `f(s)s^{-c}` and `f(t)t^{-c}` compare as the sign of `ρ - c`
says: `≤` when `ρ ≥ c`, `≥` when `ρ ≤ c`. -/
theorem Krylov.aux_mul_rpow_neg_le {f f' : ℝ → ℝ} {T c : ℝ}
    (hf : ContinuousOn f (Set.Icc 0 T)) (hd : ∀ s ∈ Set.Ioo 0 T, HasDerivAt f (f' s) s)
    (hpos : ∀ s ∈ Set.Ioc 0 T, 0 < f s) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (ht : t ≤ T) : -- --- CONCL ---
    ((∀ x ∈ Set.Ioo 0 T, c ≤ f' x * x / f x) → f s * s ^ (-c) ≤ f t * t ^ (-c)) ∧
      ((∀ x ∈ Set.Ioo 0 T, f' x * x / f x ≤ c) →
        f t * t ^ (-c) ≤ f s * s ^ (-c)) := by -- --- PROOF ---
  have hcont : ContinuousOn (fun x => f x * x ^ (-c)) (Set.Ioc 0 T) :=
    (hf.mono Set.Ioc_subset_Icc_self).mul fun x hx =>
      (Real.continuousAt_rpow_const x (-c) (Or.inl hx.1.ne')).continuousWithinAt
  have hder : ∀ x ∈ interior (Set.Ioc 0 T), HasDerivAt (fun x => f x * x ^ (-c))
      (x ^ (-c - 1) * (f' x * x - c * f x)) x := fun x hx => by
    rw [interior_Ioc] at hx
    exact Krylov.aux_hasDerivAt_mul_rpow_neg hx.1 (hd x hx)
  have hdiff : DifferentiableOn ℝ (fun x => f x * x ^ (-c)) (interior (Set.Ioc 0 T)) :=
    fun x hx => (hder x hx).differentiableAt.differentiableWithinAt
  have hmem : ∀ x ∈ Set.Ioo 0 T, 0 < x ^ (-c - 1) ∧ 0 < f x := fun x hx =>
    ⟨Real.rpow_pos_of_pos hx.1 _, hpos x ⟨hx.1, hx.2.le⟩⟩
  have hsD : s ∈ Set.Ioc 0 T := ⟨hs, hst.trans ht⟩
  have htD : t ∈ Set.Ioc 0 T := ⟨hs.trans_le hst, ht⟩
  refine ⟨fun hρ => ?_, fun hρ => ?_⟩
  · -- `ρ ≥ c`: nondecreasing
    refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 T) hcont hdiff (fun x hx => ?_) hsD htD hst
    rw [(hder x hx).deriv]
    rw [interior_Ioc] at hx
    obtain ⟨h1, h2⟩ := hmem x hx
    have := hρ x hx
    rw [le_div_iff₀ h2] at this
    exact mul_nonneg h1.le (by linarith)
  · -- `ρ ≤ c`: nonincreasing
    refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 T) hcont hdiff (fun x hx => ?_) hsD htD hst
    rw [(hder x hx).deriv]
    rw [interior_Ioc] at hx
    obtain ⟨h1, h2⟩ := hmem x hx
    have := hρ x hx
    rw [div_le_iff₀ h2] at this
    exact mul_nonpos_of_nonneg_of_nonpos h1.le (by linarith)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 6.8]: `f > 0` on `(0, T]` with `1 ≤ m̃ ≤ f'(s)s/f(s) ≤ m - 1` on `(0, T)` gives
`t/m f(t) ≤ ∫₀ᵗf ≤ t/(m̃+1) f(t) ≤ t/2 f(t)` for `0 < t ≤ T`. -/
theorem Krylov.integral_bounds_of_effectiveOrder {f f' : ℝ → ℝ} {T m' : ℝ} {m : ℕ}
    (hf : ContinuousOn f (Set.Icc 0 T)) (hd : ∀ s ∈ Set.Ioo 0 T, HasDerivAt f (f' s) s)
    (hpos : ∀ s ∈ Set.Ioc 0 T, 0 < f s) (hm' : 1 ≤ m')
    (hρ : ∀ s ∈ Set.Ioo 0 T, m' ≤ f' s * s / f s ∧ f' s * s / f s ≤ (m : ℝ) - 1)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) : -- --- CONCL ---
    t / m * f t ≤ ∫ s in (0 : ℝ)..t, f s ∧ ∫ s in (0 : ℝ)..t, f s ≤ t / (m' + 1) * f t ∧
      t / (m' + 1) * f t ≤ t / 2 * f t := by -- --- PROOF ---
  obtain ⟨ht0, htT⟩ := ht
  have hft := hpos t ⟨ht0, htT⟩
  have hm : (1 : ℝ) ≤ (m : ℝ) - 1 := hm'.trans ((hρ (t / 2) ⟨by linarith, by linarith⟩).1.trans
    (hρ (t / 2) ⟨by linarith, by linarith⟩).2)
  have hfi : IntervalIntegrable f MeasureTheory.volume 0 t :=
    (hf.mono (Set.uIcc_of_le ht0.le ▸ Set.Icc_subset_Icc_right htT)).intervalIntegrable
  -- `∫₀ᵗ C sᶜ ds = C t^{c+1}/(c+1)`
  have hpow : ∀ c : ℝ, 0 ≤ c → ∫ s in (0 : ℝ)..t, f t * t ^ (-c) * s ^ c = t / (c + 1) * f t := by
    intro c hc
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
      Real.zero_rpow (by linarith), sub_zero, Real.rpow_add ht0, Real.rpow_one,
      Real.rpow_neg ht0.le]
    field_simp
  have hpowi : ∀ c : ℝ, 0 ≤ c →
      IntervalIntegrable (fun s => f t * t ^ (-c) * s ^ c) MeasureTheory.volume 0 t := fun c hc =>
    (continuous_const.mul (Real.continuous_rpow_const hc)).intervalIntegrable _ _
  -- `f(s) = (f(s)s^{-c})sᶜ`
  have hsplit : ∀ c s : ℝ, 0 < s → f s = f s * s ^ (-c) * s ^ c := fun c s hs => by
    rw [Real.rpow_neg hs.le, mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos hs c).ne', mul_one]
  refine ⟨?_, ?_, ?_⟩
  · -- `ρ ≤ m - 1`: `f(s) ≥ f(t)(s/t)^{m-1}`
    have h := intervalIntegral.integral_mono_on_of_le_Ioo ht0.le (hpowi ((m : ℝ) - 1) (by linarith))
      hfi
      fun s hs => by
        rw [hsplit ((m : ℝ) - 1) s hs.1]
        exact mul_le_mul_of_nonneg_right ((Krylov.aux_mul_rpow_neg_le hf hd hpos hs.1 hs.2.le
          htT).2 fun x hx => (hρ x hx).2) (Real.rpow_pos_of_pos hs.1 _).le
    rw [hpow ((m : ℝ) - 1) (by linarith), sub_add_cancel] at h
    exact h
  · -- `ρ ≥ m̃`: `f(s) ≤ f(t)(s/t)^{m̃}`
    have h := intervalIntegral.integral_mono_on_of_le_Ioo ht0.le hfi (hpowi m' (by linarith))
      fun s hs => by
        rw [hsplit m' s hs.1]
        exact mul_le_mul_of_nonneg_right ((Krylov.aux_mul_rpow_neg_le hf hd hpos hs.1 hs.2.le
          htT).1 fun x hx => (hρ x hx).1) (Real.rpow_pos_of_pos hs.1 _).le
    rwa [hpow m' (by linarith)] at h
  · -- `m̃ ≥ 1`
    have h2 : t / (m' + 1) ≤ t / 2 := div_le_div_of_nonneg_left ht0.le (by norm_num) (by linarith)
    exact mul_le_mul_of_nonneg_right h2 hft.le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
