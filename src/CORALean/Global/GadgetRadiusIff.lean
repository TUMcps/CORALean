module

public import CORALean.Global.CoeffNormHalfGadgetH
public import CORALean.Global.GadgetGA
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The reduction's containment radius is one iff the `p ↦ 1` norm is

[1, Lemma 27], at the circumbody `Z(½H)` the proof works with: for `p ∈ (1, ∞]`, `G_A` of Eq. 65
with the radii `L, ϱ` of [1, Lemma 26], and `ξ = ‖A‖_{p↦1}`, `r(E_p(G_A), Z(½H)) = 1` iff `ξ = 1`,
and likewise with `<` and `>`. The printed `Z(H)` is twice as large
(`gadget_radius_iff_counterexample`). Through the closed-form norm of `Z(½H)`
(`coeffNorm_half_gadgetH`) the radius is the maximum of `max(‖A α'‖_∞, (‖A α'‖₁ + L|s|)/n)` over
`‖(α', s)‖_p ≤ 1`, and with `‖A α'‖₁ ≤ ξ‖α'‖_p` the question is whether `a + L s ≤ n` on
`aᵖ + sᵖ ≤ 1`: Eq. 66 and 67 make the tangent planes of `t ↦ tᵖ` at `ϱ` and `x = (n - ϱ)/L` bound
it, attained at `(ϱ v, x)`. At `p = ∞`, `L = n - 1` and `a, s ≤ 1`.

## Inputs
* `p` – norm exponent
* `L` – first gadget radius
* `ϱ` – second gadget radius
* `A` – matrix to be reduced
* `ξ` – induced norm of the matrix
* `r` – containment radius

## Hypotheses
* `hn` – the dimension is at least two
* `hp` – the exponent exceeds one
* `hL` – the radii satisfy the gadget equations
* `hξ` – the induced norm is the greatest 1-norm image over the unit ball
* `hr` – the radius is the greatest coefficient norm over the unit ball

## Conclusion
* the radius equals, is below or is above one exactly when the induced norm is

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal
open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The tangent of `t ↦ tᵠ` at `c > 0` lies below it, `q ≥ 1`. -/
theorem aux_rpow_tangent_le {q c u : ℝ} (hq : 1 ≤ q) (hc : 0 < c) (hu : 0 ≤ u) :
    c ^ q + q * c ^ (q - 1) * (u - c) ≤ u ^ q := by -- --- PROOF ---
  have hb := one_add_mul_self_le_rpow_one_add (s := u / c - 1) (by
    have : 0 ≤ u / c := div_nonneg hu hc.le
    linarith) hq
  rw [add_sub_cancel, Real.div_rpow hu hc.le, le_div_iff₀ (Real.rpow_pos_of_pos hc q)] at hb
  have hcq : c ^ q = c ^ (q - 1) * c := by
    rw [← Real.rpow_add_one hc.ne', sub_add_cancel]
  calc c ^ q + q * c ^ (q - 1) * (u - c)
      = (1 + q * (u / c - 1)) * c ^ q := by rw [hcq]; field_simp
    _ ≤ u ^ q := hb

/-- With Eq. 66 and 67, `a + L s ≤ n` on `aᵠ + sᵠ ≤ 1`. -/
theorem aux_add_mul_le {q L ϱ N a s : ℝ} (hq : 1 < q) (hϱ : 0 < ϱ) (hLpos : 0 < L)
    (hx : 0 < (N - ϱ) / L) (h66 : 1 - ϱ ^ q = ((N - ϱ) / L) ^ q)
    (h67 : L = (1 - ((N - ϱ) / L) ^ q) ^ (1 / q - 1) * ((N - ϱ) / L) ^ (q - 1))
    (ha : 0 ≤ a) (hs : 0 ≤ s) (has : a ^ q + s ^ q ≤ 1) : -- --- CONCL ---
    a + L * s ≤ N ∧ ϱ ^ q + ((N - ϱ) / L) ^ q = 1 := by -- --- PROOF ---
  set x := (N - ϱ) / L with hxdef
  have hsum : ϱ ^ q + x ^ q = 1 := by linarith
  -- `L = ϱ^{1-q} x^{q-1}`, and `N = ϱ + L x = ϱ^{1-q}`
  have hL : L = ϱ ^ (1 - q) * x ^ (q - 1) := by
    rw [h67, ← h66, sub_sub_cancel, ← Real.rpow_mul hϱ.le]
    congr 2
    field_simp
  have hN : N = ϱ ^ (1 - q) := by
    have hLx : L * x = N - ϱ := by rw [hxdef]; field_simp
    have hxq : x ^ (q - 1) * x = x ^ q := by
      rw [← Real.rpow_add_one hx.ne', sub_add_cancel]
    have hϱq : ϱ ^ (1 - q) * ϱ ^ q = ϱ := by
      rw [← Real.rpow_add hϱ, sub_add_cancel, Real.rpow_one]
    have : N - ϱ = ϱ ^ (1 - q) * x ^ q := by rw [← hLx, hL, mul_assoc, hxq]
    have h2 : ϱ ^ (1 - q) * x ^ q = ϱ ^ (1 - q) - ϱ := by
      rw [← h66, mul_sub, mul_one, hϱq]
    linarith
  refine ⟨?_, hsum⟩
  -- the tangent planes at `ϱ` and `x`
  have t1 := aux_rpow_tangent_le hq.le hϱ ha
  have t2 := aux_rpow_tangent_le hq.le hx hs
  have hq0 : 0 < q := by linarith
  have hlin : ϱ ^ (q - 1) * a + x ^ (q - 1) * s ≤ 1 := by
    have hϱq : ϱ ^ (q - 1) * ϱ = ϱ ^ q := by rw [← Real.rpow_add_one hϱ.ne', sub_add_cancel]
    have hxq : x ^ (q - 1) * x = x ^ q := by rw [← Real.rpow_add_one hx.ne', sub_add_cancel]
    have : q * (ϱ ^ (q - 1) * (a - ϱ) + x ^ (q - 1) * (s - x)) ≤ 0 := by nlinarith
    have h' : ϱ ^ (q - 1) * (a - ϱ) + x ^ (q - 1) * (s - x) ≤ 0 := by
      by_contra hc
      nlinarith [mul_pos hq0 (lt_of_not_ge hc)]
    nlinarith
  have hinv : ϱ ^ (1 - q) * ϱ ^ (q - 1) = 1 := by
    rw [← Real.rpow_add hϱ]; norm_num
  have hpos : 0 < ϱ ^ (1 - q) := Real.rpow_pos_of_pos hϱ _
  calc a + L * s = ϱ ^ (1 - q) * (ϱ ^ (q - 1) * a + x ^ (q - 1) * s) := by
        rw [hL, mul_add, ← mul_assoc, hinv, one_mul, mul_assoc]
    _ ≤ ϱ ^ (1 - q) * 1 := mul_le_mul_of_nonneg_left hlin hpos.le
    _ = N := by rw [mul_one, hN]

/-- The supremum norm is below the `1`-norm. -/
theorem aux_norm_le_sum_abs' (y : Vec ℝ n) : ‖y‖ ≤ ∑ i, |y i| :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).mpr fun i =>
    (Real.norm_eq_abs _).trans_le
      (Finset.single_le_sum (f := fun i => |y i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

/-- `‖A v‖₁ ≤ ξ ‖v‖_p` for `ξ` the maximum on the unit ball. -/
theorem aux_sum_abs_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (A : Mat ℝ n m) {ξ : ℝ}
    (hξ : IsGreatest ((fun v : PiLp p (fun _ : Fin m => ℝ) => ∑ i, |(A *ᵥ WithLp.ofLp v) i|) ''
      Metric.closedBall 0 1) ξ) (v : PiLp p (fun _ : Fin m => ℝ)) :
    ∑ i, |(A *ᵥ WithLp.ofLp v) i| ≤ ξ * ‖v‖ := by -- --- PROOF ---
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw := hξ.2 ⟨‖v‖⁻¹ • v, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hpos.ne'], rfl⟩
  simp only [WithLp.ofLp_smul, mulVec_smul, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv,
    abs_norm, ← Finset.mul_sum] at hw
  rw [inv_mul_le_iff₀ hpos] at hw
  linarith


/-- The hypotheses on the radii: Eq. 66 and 67 at finite `p`, `L = n - 1`, `ϱ = 1` at `p = ∞`. -/
def aux_Radii (n : ℕ) (p : ℝ≥0∞) (L ϱ : ℝ) : Prop :=
  (p = ∞ ∧ L = n - 1 ∧ ϱ = 1) ∨ (p ≠ ∞ ∧ n - 1 < L ∧ L < n ∧ 0 < ϱ ∧ ϱ < 1 ∧
    1 - ϱ ^ p.toReal = ((n - ϱ) / L) ^ p.toReal ∧
    L = (1 - ((n - ϱ) / L) ^ p.toReal) ^ (1 / p.toReal - 1) * ((n - ϱ) / L) ^ (p.toReal - 1))

/-- Every coefficient in the ball has `‖α'‖ ≤ 1`, `|s| ≤ 1` and `‖α'‖ + L|s| ≤ n`. -/
theorem aux_cons (hn : 2 ≤ n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) {L ϱ : ℝ}
    (hL : aux_Radii n p L ϱ) (α : WithLp p (PiLp p (fun _ : Fin m => ℝ) × ℝ)) (hα : ‖α‖ ≤ 1) :
    ‖α.fst‖ ≤ 1 ∧ |α.snd| ≤ 1 ∧ ‖α.fst‖ + L * |α.snd| ≤ n := by -- --- PROOF ---
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rcases hL with ⟨rfl, rfl, -⟩ | ⟨hpt, hL1, -, hϱ, hϱ1, h66, h67⟩
  · rw [WithLp.prod_norm_eq_sup, max_le_iff, Real.norm_eq_abs] at hα
    refine ⟨hα.1, hα.2, ?_⟩
    have := mul_le_mul_of_nonneg_left hα.2 (by linarith : (0 : ℝ) ≤ n - 1)
    linarith [hα.1]
  -- finite `p`: `‖α'‖ᵖ + |s|ᵖ ≤ 1`, and Eq. 66-67 bound `‖α'‖ + L|s|`
  · have hq : 1 < p.toReal := by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt).mpr hp
      rwa [ENNReal.toReal_one] at this
    have hq0 : 0 < p.toReal := by linarith
    rw [WithLp.prod_norm_eq_add hq0, Real.norm_eq_abs] at hα
    have hsum : ‖α.fst‖ ^ p.toReal + |α.snd| ^ p.toReal ≤ 1 := by
      by_contra hc
      exact absurd hα (not_le.mpr (Real.one_lt_rpow (lt_of_not_ge hc) (by positivity)))
    have hle1 : ∀ t : ℝ, t ^ p.toReal ≤ 1 → t ≤ 1 := fun t h => by
      by_contra hc
      exact absurd h (not_le.mpr (Real.one_lt_rpow (lt_of_not_ge hc) hq0))
    have ha := Real.rpow_nonneg (norm_nonneg α.fst) p.toReal
    have hs := Real.rpow_nonneg (abs_nonneg α.snd) p.toReal
    refine ⟨hle1 _ (by linarith), hle1 _ (by linarith), ?_⟩
    have hLpos : 0 < L := by linarith
    have hx : 0 < (n - ϱ) / L := div_pos (by linarith) hLpos
    exact (aux_add_mul_le hq hϱ hLpos hx h66 h67 (norm_nonneg _) (abs_nonneg _) hsum).1

/-- The radii are positive and `L < n`. -/
theorem aux_radii_pos (hn : 2 ≤ n) {p : ℝ≥0∞} {L ϱ : ℝ} (hL : aux_Radii n p L ϱ) :
    0 < ϱ ∧ ϱ < n ∧ 0 < L ∧ L < n := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rcases hL with ⟨-, rfl, rfl⟩ | ⟨-, h1, h2, h3, h4, -⟩
  · exact ⟨one_pos, by linarith, by linarith, by linarith⟩
  · exact ⟨h3, by linarith, by linarith, h2⟩

/-- The upper bounds at every coefficient of the ball. -/
theorem aux_radius_upper (hn : 2 ≤ n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) {L ϱ : ℝ}
    (hL : aux_Radii n p L ϱ) (A : Mat ℝ n m) {ξ : ℝ}
    (hξ : IsGreatest ((fun v : PiLp p (fun _ : Fin m => ℝ) => ∑ i, |(A *ᵥ WithLp.ofLp v) i|) ''
      Metric.closedBall 0 1) ξ)
    (α : WithLp p (PiLp p (fun _ : Fin m => ℝ) × ℝ)) (hα : ‖α‖ ≤ 1) : -- --- CONCL ---
    (ξ ≤ 1 → coeffNorm ((1 / 2 : ℝ) • gadgetH n) (gadgetGA p A L α) ≤ 1) ∧
      (ξ < 1 → coeffNorm ((1 / 2 : ℝ) • gadgetH n) (gadgetGA p A L α) < 1) := by -- --- PROOF ---
  have hnpos : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
  obtain ⟨-, -, hLpos, hLn⟩ := aux_radii_pos hn hL
  obtain ⟨ha1, hs1, hsum⟩ := aux_cons hn hp hL α hα
  have hA := aux_sum_abs_le A hξ α.fst
  have hsup := aux_norm_le_sum_abs' (A *ᵥ WithLp.ofLp α.fst)
  have habs : |-L * α.snd| = L * |α.snd| := by rw [abs_mul, abs_neg, abs_of_pos hLpos]
  rw [(coeffNorm_half_gadgetH (by omega)).2, show (gadgetGA p A L α).2 = -L * α.snd from rfl,
    habs]
  set a := ‖α.fst‖
  set S := ∑ i, |(gadgetGA p A L α).1 i|
  have hS : S = ∑ i, |(A *ᵥ WithLp.ofLp α.fst) i| := rfl
  have ha0 : 0 ≤ a := norm_nonneg _
  have hs0 := abs_nonneg α.snd
  have hLs : L * |α.snd| ≤ L := mul_le_of_le_one_right hLpos.le hs1
  -- the two terms of the closed form, each against `1`
  refine ⟨fun h => max_le ?_ ?_, fun h => max_lt ?_ ?_⟩
  · have : ξ * a ≤ 1 := mul_le_one₀ h ha0 ha1
    exact hsup.trans (hA.trans this)
  · rw [div_le_one hnpos, hS]
    have : ξ * a ≤ a := mul_le_of_le_one_left ha0 h
    linarith
  · have : ξ * a < 1 := by
      rcases ha0.lt_or_eq with hapos | ha00
      · exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h hapos) (by rw [one_mul]; exact ha1)
      · rw [← ha00, mul_zero]; exact one_pos
    exact lt_of_le_of_lt (hsup.trans hA) this
  -- strictly: `ξ a < a` unless `a = 0`, and then `L|s| ≤ L < n`
  · rw [div_lt_one hnpos, hS]
    rcases ha0.lt_or_eq with hapos | ha00
    · have : ξ * a < a := by
        have := mul_lt_mul_of_pos_right h hapos
        rwa [one_mul] at this
      linarith
    · rw [← ha00, mul_zero] at hA
      linarith

/-- The lower bound, at `(ϱ v, -x)` for a maximizer `v` of `‖A v‖₁`. -/
theorem aux_lower (hn : 2 ≤ n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) {L ϱ : ℝ}
    (hL : aux_Radii n p L ϱ) (A : Mat ℝ n m) {ξ : ℝ}
    (hξ : IsGreatest ((fun v : PiLp p (fun _ : Fin m => ℝ) => ∑ i, |(A *ᵥ WithLp.ofLp v) i|) ''
      Metric.closedBall 0 1) ξ) : -- --- CONCL ---
    ∃ α : WithLp p (PiLp p (fun _ : Fin m => ℝ) × ℝ), ‖α‖ ≤ 1 ∧
      (ϱ * ξ + n - ϱ) / n ≤
        coeffNorm ((1 / 2 : ℝ) • gadgetH n) (gadgetGA p A L α) := by -- --- PROOF ---
  have hnpos : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
  obtain ⟨hϱ, hϱn, hLpos, -⟩ := aux_radii_pos hn hL
  obtain ⟨v, hv, hvξ⟩ := hξ.1
  rw [Metric.mem_closedBall, dist_zero_right] at hv
  set x := (n - ϱ) / L with hxdef
  have hx : 0 < x := div_pos (by linarith) hLpos
  have hLx : L * x = n - ϱ := by rw [hxdef]; field_simp
  have hfst : ‖ϱ • v‖ ≤ ϱ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hϱ]
    exact mul_le_of_le_one_right hϱ.le hv
  -- `(ϱ v, -x)` is in the ball by Eq. 66, its value `(ϱ ξ + L x)/n`
  refine ⟨WithLp.toLp p (ϱ • v, -x), ?_, ?_⟩
  · rcases hL with ⟨rfl, rfl, rfl⟩ | ⟨hpt, -, -, -, -, h66, -⟩
    · rw [WithLp.prod_norm_eq_sup]
      refine max_le (hfst.trans le_rfl) ?_
      show ‖-x‖ ≤ 1
      rw [norm_neg, Real.norm_eq_abs, abs_of_pos hx, hxdef, div_le_one hLpos]
    · have hq0 : 0 < p.toReal := ENNReal.toReal_pos (by
        rintro rfl; exact absurd hp (not_lt.mpr zero_le_one)) hpt
      rw [WithLp.prod_norm_eq_add hq0]
      refine Real.rpow_le_one (by positivity) ?_ (by positivity)
      show ‖ϱ • v‖ ^ p.toReal + ‖-x‖ ^ p.toReal ≤ 1
      rw [norm_neg, Real.norm_eq_abs, abs_of_pos hx]
      have := Real.rpow_le_rpow (norm_nonneg _) hfst hq0.le
      linarith
  -- the value through the closed form's second term
  · rw [(coeffNorm_half_gadgetH (by omega)).2]
    refine le_trans ?_ (le_max_right _ _)
    show (ϱ * ξ + n - ϱ) / n ≤ (∑ i, |(A *ᵥ WithLp.ofLp (ϱ • v)) i| + |-L * -x|) / n
    rw [div_le_div_iff_of_pos_right hnpos, neg_mul_neg, abs_of_pos (mul_pos hLpos hx), hLx]
    simp only [WithLp.ofLp_smul, mulVec_smul, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos hϱ, ← Finset.mul_sum]
    rw [show ∑ i, |(A *ᵥ WithLp.ofLp v) i| = ξ from hvξ]
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem gadget_radius_iff (hn : 2 ≤ n) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (L ϱ : ℝ)
    (hL : (p = ∞ ∧ L = n - 1 ∧ ϱ = 1) ∨ (p ≠ ∞ ∧ n - 1 < L ∧ L < n ∧ 0 < ϱ ∧ ϱ < 1 ∧
      1 - ϱ ^ p.toReal = ((n - ϱ) / L) ^ p.toReal ∧
      L = (1 - ((n - ϱ) / L) ^ p.toReal) ^ (1 / p.toReal - 1) * ((n - ϱ) / L) ^ (p.toReal - 1)))
    (A : Mat ℝ n m) {ξ : ℝ}
    (hξ : IsGreatest ((fun v : PiLp p (fun _ : Fin m => ℝ) => ∑ i, |(A *ᵥ WithLp.ofLp v) i|) ''
      Metric.closedBall 0 1) ξ) {r : ℝ}
    (hr : IsGreatest ((fun α => coeffNorm ((1 / 2 : ℝ) • gadgetH n) (gadgetGA p A L α)) ''
      Metric.closedBall 0 1) r) : -- --- CONCL ---
    (r = 1 ↔ ξ = 1) ∧ (r < 1 ↔ ξ < 1) ∧ (1 < r ↔ 1 < ξ) := by -- --- PROOF ---
  have hnpos : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
  obtain ⟨hϱ, hϱn, -, -⟩ := aux_radii_pos hn hL
  -- the radius is the value at a maximizer, and at least the value at `(ϱ v, -x)`
  obtain ⟨α', hα', hrα⟩ := hr.1
  rw [Metric.mem_closedBall, dist_zero_right] at hα'
  obtain ⟨α₀, hα₀, hlow⟩ := aux_lower hn hp hL A hξ
  have hr0 : coeffNorm ((1 / 2 : ℝ) • gadgetH n) (gadgetGA p A L α₀) ≤ r :=
    hr.2 ⟨α₀, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
  have h1 : ξ ≤ 1 → r ≤ 1 := fun h => hrα ▸ (aux_radius_upper hn hp hL A hξ α' hα').1 h
  have h2 : ξ < 1 → r < 1 := fun h => hrα ▸ (aux_radius_upper hn hp hL A hξ α' hα').2 h
  -- `ξ ≥ 1` reaches `1` at `(ϱ v, -x)`, `L x = n - ϱ`
  have h3 : 1 ≤ ξ → 1 ≤ r := fun h => by
    refine le_trans ?_ (hlow.trans hr0)
    rw [le_div_iff₀ hnpos]
    have := mul_le_mul_of_nonneg_left h hϱ.le
    linarith
  have h4 : 1 < ξ → 1 < r := fun h => by
    refine lt_of_lt_of_le ?_ (hlow.trans hr0)
    rw [lt_div_iff₀ hnpos]
    have := mul_lt_mul_of_pos_left h hϱ
    linarith
  -- the trichotomy in `ξ` gives all three equivalences
  rcases lt_trichotomy ξ 1 with hξ1 | hξ1 | hξ1
  · have := h2 hξ1
    exact ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun _ => hξ1, fun _ => this⟩,
      ⟨fun h => by linarith, fun h => by linarith⟩⟩
  · have := le_antisymm (h1 hξ1.le) (h3 hξ1.ge)
    exact ⟨⟨fun _ => hξ1, fun _ => this⟩, ⟨fun h => by linarith, fun h => by linarith⟩,
      ⟨fun h => by linarith, fun h => by linarith⟩⟩
  · have := h4 hξ1
    exact ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun h => by linarith,
      fun h => by linarith⟩, ⟨fun _ => hξ1, fun _ => this⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
