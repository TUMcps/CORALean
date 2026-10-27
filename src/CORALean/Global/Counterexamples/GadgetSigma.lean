module

public import CORALean.Global.CoeffNorm
public import CORALean.Global.CoeffNormHalfGadgetH
public import CORALean.Global.GadgetGA
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The slope bound on the reduction's radius function fails

[1, Prop. 28], Eq. 80: for `σ(ξ) = r(E_p(G_{A/ξ}), Z(H))` and `ξ̂ = m^{(p-1)/p} ‖A‖_{1↦1}`,
`|σ(ξ') - σ(ξ)| ≥ (‖A‖_{1↦∞} / ξ̂²) |ξ - ξ'|` on `(0, ξ̂]`. The proof bounds `σ(ξ)` below by
`‖A‖_{1↦∞}/ξ` (Eq. 84) and `|1/ξ - 1/ξ'|` below (Eq. 85), which together bound no difference of
`σ`. At `n = 2`, `m = 1`, `p = ∞`, `L = n - 1 = 1` ([1, Lemma 26]) and `A = (2, 1)ᵀ`:
`‖A‖_{1↦∞} = 2`, `‖A‖_{1↦1} = 3 = ξ̂`, and through the closed-form norm of `Z(½H)` the radius is
`(3/ξ + 1)/2` for `ξ ≥ 1`: `σ(3) = 1`, `σ(5/2) = 11/10`, a difference `1/10 < (2/9) · (1/2)`. At
the printed `Z(H)` every radius halves, and the bound fails the more; it fails at the
circumbody `Z(½H)` the proof uses as well.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the radii at two scalings differ by less than the printed slope bound allows

## References

* [1] [A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control,
      2025.](../../../../references/2025/kulmburg-tac-approximability-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal
open Matrix


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `A = (2, 1)ᵀ ∈ ℝ^{2×1}`. -/
@[step_of gadget_sigma_counterexample]
def step_A28 : Mat ℝ 2 1 := fun i _ => if i = 0 then 2 else 1


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_mulVec28 (t : ℝ) (w : Fin 1 → ℝ) : -- --- CONCL ---
    (t • step_A28) *ᵥ w = ![2 * t * w 0, t * w 0] := by -- --- PROOF ---
  funext i
  simp only [mulVec, dotProduct, Fin.sum_univ_one, Matrix.smul_apply, smul_eq_mul, step_A28]
  fin_cases i
  · simp only [Fin.zero_eta, if_true, cons_val_zero]; ring
  · simp only [Fin.mk_one, one_ne_zero, if_false, cons_val_one, cons_val_zero]; ring

/-- A bound on both entries bounds the supremum norm. -/
private theorem aux_norm_vec2_le {a b c : ℝ} (hc : 0 ≤ c) (ha : |a| ≤ c) (hb : |b| ≤ c) :
    ‖(![a, b] : Vec ℝ 2)‖ ≤ c := by
  refine (pi_norm_le_iff_of_nonneg hc).mpr fun i => ?_
  fin_cases i
  · simpa using ha
  · simpa using hb

/-- `H = 2 (½H)`, so its norm is half. -/
private theorem aux_coeffNorm_gadgetH (x : Vec ℝ 2 × ℝ) : -- --- CONCL ---
    coeffNorm (gadgetH 2) x = coeffNorm ((1 / 2 : ℝ) • gadgetH 2) x / 2 := by -- --- PROOF ---
  have hs := (coeffNorm_half_gadgetH (n := 2) (by norm_num)).1
  obtain ⟨β, hβ, hβn⟩ := exists_coeffNorm_eq _ (hs x)
  have hHβ : gadgetH 2 ((1 / 2 : ℝ) • β) = x := by rw [map_smul]; exact hβ
  obtain ⟨γ, hγ, hγn⟩ := exists_coeffNorm_eq (gadgetH 2) ⟨_, hHβ⟩
  refine le_antisymm ?_ ?_
  · -- `½ β` reaches `x` through `H`
    calc coeffNorm (gadgetH 2) x = coeffNorm (gadgetH 2) (gadgetH 2 ((1 / 2 : ℝ) • β)) := by
          rw [hHβ]
      _ ≤ ‖(1 / 2 : ℝ) • β‖ := coeffNorm_le _ _
      _ = coeffNorm ((1 / 2 : ℝ) • gadgetH 2) x / 2 := by
          rw [norm_smul, hβn, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          ring
  · -- and `2 γ` through `½H`
    have h2γ : ((1 / 2 : ℝ) • gadgetH 2) ((2 : ℝ) • γ) = x := by
      rw [LinearMap.smul_apply, map_smul, hγ, smul_smul]; norm_num
    have h := coeffNorm_le ((1 / 2 : ℝ) • gadgetH 2) ((2 : ℝ) • γ)
    rw [h2γ, norm_smul, hγn, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith

/-- For `0 < t ≤ 1` the radius of `E_∞(G_{tA})` at `Z(½H)` is `(3t + 1)/2`, attained at
`(1, -1)`. -/
private theorem aux_sigma (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) : -- --- CONCL ---
    IsGreatest ((fun α => coeffNorm ((1 / 2 : ℝ) • gadgetH 2) (gadgetGA ∞ (t • step_A28) 1 α)) ''
      Metric.closedBall 0 1) ((3 * t + 1) / 2) := by -- --- PROOF ---
  have hnorm := (coeffNorm_half_gadgetH (n := 2) (by norm_num)).2
  -- the value at `(v, s)`
  have hval : ∀ α : WithLp ∞ (PiLp ∞ (fun _ : Fin 1 => ℝ) × ℝ),
      coeffNorm ((1 / 2 : ℝ) • gadgetH 2) (gadgetGA ∞ (t • step_A28) 1 α) =
        max ‖(![2 * t * α.fst 0, t * α.fst 0] : Vec ℝ 2)‖
          ((|2 * t * α.fst 0| + |t * α.fst 0| + |α.snd|) / 2) := by
    intro α
    rw [show gadgetGA ∞ (t • step_A28) 1 α = (![2 * t * α.fst 0, t * α.fst 0], -1 * α.snd) from
      Prod.ext (aux_mulVec28 t _) rfl, hnorm]
    simp [Fin.sum_univ_two]
  -- the bound at every coefficient of the ball
  have hle : ∀ v s : ℝ, |v| ≤ 1 → |s| ≤ 1 →
      max ‖(![2 * t * v, t * v] : Vec ℝ 2)‖ ((|2 * t * v| + |t * v| + |s|) / 2) ≤
        (3 * t + 1) / 2 := by
    intro v s hv hs
    have h1 : |2 * t * v| ≤ 2 * t := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos ht0]; nlinarith [abs_nonneg v]
    have h2 : |t * v| ≤ t := by
      rw [abs_mul, abs_of_pos ht0]; nlinarith [abs_nonneg v]
    refine max_le (aux_norm_vec2_le (by linarith) (by linarith) (by linarith)) ?_
    linarith
  -- attained at `(1, -1)`, a point of the ball
  refine ⟨⟨WithLp.toLp ∞ (WithLp.toLp ∞ (fun _ => 1), -1), ?_, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, WithLp.prod_norm_eq_sup]
    refine max_le ?_ (by simp)
    show ‖WithLp.toLp ∞ (fun _ : Fin 1 => (1 : ℝ))‖ ≤ 1
    rw [PiLp.norm_toLp]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp
  · show coeffNorm ((1 / 2 : ℝ) • gadgetH 2) (gadgetGA ∞ (t • step_A28) 1 _) = _
    rw [hval]
    refine le_antisymm (hle 1 (-1) (by simp) (by simp)) (le_trans ?_ (le_max_right _ _))
    show (3 * t + 1) / 2 ≤ (|2 * t * 1| + |t * 1| + |(-1 : ℝ)|) / 2
    rw [mul_one, mul_one, abs_of_pos (by linarith), abs_of_pos ht0, abs_neg, abs_one]
    linarith
  -- and the bound over the whole ball
  · rintro _ ⟨α, hα, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, WithLp.prod_norm_eq_sup, max_le_iff] at hα
    have hv : |α.fst 0| ≤ 1 := (Real.norm_eq_abs _ ▸ PiLp.norm_apply_le α.fst 0).trans hα.1
    have hs : |α.snd| ≤ 1 := by rw [← Real.norm_eq_abs]; exact hα.2
    show coeffNorm ((1 / 2 : ℝ) • gadgetH 2) (gadgetGA ∞ (t • step_A28) 1 α) ≤ _
    rw [hval]
    exact hle _ _ hv hs


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `A = (2, 1)ᵀ`, `p = ∞`, `L = 1`, with `‖A‖_{1↦∞} = 2` and `ξ̂ = ‖A‖_{1↦1} = 3`, the radii
`σ(3)` and `σ(5/2)` at the printed `Z(H)`, and at `Z(½H)`, differ by less than
`(2 / ξ̂²) |3 - 5/2|`. -/
theorem gadget_sigma_counterexample : -- --- CONCL ---
    -- `‖A‖_{1↦∞} = 2`, the numerator of Eq. 80's slope
    IsGreatest ((fun v : PiLp 1 (fun _ : Fin 1 => ℝ) => ‖step_A28 *ᵥ WithLp.ofLp v‖) ''
        Metric.closedBall 0 1) 2 ∧
      -- `‖A‖_{1↦1} = 3 = ξ̂` at `m = 1`
      IsGreatest ((fun v : PiLp 1 (fun _ : Fin 1 => ℝ) => ∑ i, |(step_A28 *ᵥ WithLp.ofLp v) i|) ''
        Metric.closedBall 0 1) 3 ∧
      -- at the printed `Z(H)`, `σ(3)`, `σ(5/2)` differ by less than the slope bound: Eq. 80 fails
      (∃ σ σ' : ℝ, IsGreatest ((fun α => coeffNorm (gadgetH 2)
          (gadgetGA ∞ ((3 : ℝ)⁻¹ • step_A28) 1 α)) '' Metric.closedBall 0 1) σ ∧
        IsGreatest ((fun α => coeffNorm (gadgetH 2)
          (gadgetGA ∞ ((5 / 2 : ℝ)⁻¹ • step_A28) 1 α)) '' Metric.closedBall 0 1) σ' ∧
        |σ' - σ| < 2 / 3 ^ 2 * |3 - 5 / 2|) ∧
      -- the same at the circumbody `Z(½H)` the proof uses, refuting the printed reading directly
      ∃ σ σ' : ℝ, IsGreatest ((fun α => coeffNorm ((1 / 2 : ℝ) • gadgetH 2)
          (gadgetGA ∞ ((3 : ℝ)⁻¹ • step_A28) 1 α)) '' Metric.closedBall 0 1) σ ∧
        IsGreatest ((fun α => coeffNorm ((1 / 2 : ℝ) • gadgetH 2)
          (gadgetGA ∞ ((5 / 2 : ℝ)⁻¹ • step_A28) 1 α)) '' Metric.closedBall 0 1) σ' ∧
        |σ' - σ| < 2 / 3 ^ 2 * |3 - 5 / 2| := by -- --- PROOF ---
  have hA : ∀ w : Fin 1 → ℝ, step_A28 *ᵥ w = ![2 * w 0, w 0] := fun w => by
    have := aux_mulVec28 1 w
    rw [one_smul] at this
    rw [this]; simp
  -- the radius at `Z(H)` is half that at `Z(½H)`
  have hhalf : ∀ t : ℝ, 0 < t → t ≤ 1 → IsGreatest ((fun α => coeffNorm (gadgetH 2)
      (gadgetGA ∞ (t • step_A28) 1 α)) '' Metric.closedBall 0 1) ((3 * t + 1) / 2 / 2) := by
    intro t ht0 ht1
    have h := aux_sigma t ht0 ht1
    have hfun : (fun α => coeffNorm (gadgetH 2) (gadgetGA ∞ (t • step_A28) 1 α)) =
        fun α => coeffNorm ((1 / 2 : ℝ) • gadgetH 2) (gadgetGA ∞ (t • step_A28) 1 α) / 2 :=
      funext fun α => aux_coeffNorm_gadgetH _
    rw [hfun]
    refine ⟨?_, ?_⟩
    · obtain ⟨α, hα, he⟩ := h.1
      exact ⟨α, hα, by simp only at he ⊢; rw [he]⟩
    · rintro _ ⟨α, hα, rfl⟩
      have := h.2 ⟨α, hα, rfl⟩
      simp only at this ⊢
      linarith
  -- the unit coefficient of `ℝ¹` with the `1`-norm
  have hone : PiLp.single 1 (0 : Fin 1) (1 : ℝ) ∈
      Metric.closedBall (0 : PiLp 1 (fun _ : Fin 1 => ℝ)) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, PiLp.norm_single, norm_one]
  have hv0 : ∀ v : PiLp 1 (fun _ : Fin 1 => ℝ), v ∈ Metric.closedBall 0 1 → |v 0| ≤ 1 :=
    fun v hv => by
      rw [Metric.mem_closedBall, dist_zero_right] at hv
      exact (Real.norm_eq_abs _ ▸ PiLp.norm_apply_le v 0).trans hv
  -- the operator norms of `A`, then the two pairs of radii
  refine ⟨⟨⟨_, hone, ?_⟩, ?_⟩, ⟨⟨_, hone, ?_⟩, ?_⟩,
    ⟨_, _, hhalf 3⁻¹ (by norm_num) (by norm_num), hhalf (5 / 2)⁻¹ (by norm_num) (by norm_num), ?_⟩,
    ⟨_, _, aux_sigma 3⁻¹ (by norm_num) (by norm_num),
      aux_sigma (5 / 2)⁻¹ (by norm_num) (by norm_num), ?_⟩⟩
  · show ‖step_A28 *ᵥ Pi.single 0 1‖ = 2
    rw [hA]
    simp only [Pi.single_eq_same, mul_one]
    have := norm_le_pi_norm (![(2 : ℝ), 1] : Vec ℝ 2) 0
    refine le_antisymm (aux_norm_vec2_le (by norm_num) (by simp) (by simp)) (by simpa using this)
  · rintro _ ⟨v, hv, rfl⟩
    show ‖step_A28 *ᵥ WithLp.ofLp v‖ ≤ 2
    rw [hA]
    have h := hv0 v hv
    refine aux_norm_vec2_le (by norm_num) ?_ (h.trans (by norm_num))
    rw [abs_mul, abs_two]
    exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans (by norm_num)
  -- `‖A‖_{1↦1} = 3`, attained at the unit coefficient
  · show ∑ i, |(step_A28 *ᵥ Pi.single 0 1) i| = 3
    rw [hA]; simp [Fin.sum_univ_two]; norm_num
  · rintro _ ⟨v, hv, rfl⟩
    show ∑ i, |(step_A28 *ᵥ WithLp.ofLp v) i| ≤ 3
    rw [hA]
    have h := hv0 v hv
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, abs_mul, abs_two]
    exact (by linarith : 2 * |v 0| + |v 0| ≤ 3)
  · norm_num [abs_of_pos]
  · norm_num [abs_of_pos]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
