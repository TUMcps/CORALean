module

public import CORALean.Global.CoeffNorm
public import CORALean.Global.CoeffNormHalfGadgetH
public import CORALean.Global.GadgetGA

@[expose] public section

/-!
# The printed circumbody `Z(H)` of the reduction is too large

[1, Lemma 27] states `r(E_p(G_A), Z(H)) = 1` iff `‖A‖_{p↦1} = 1`, with `H` of [1, Eq. 63]; but
`Ẑ = Z(½H, n e_{n+1})` [1, Lemma 25], and the proof works with `Z(½H)` (as do the slices of its
Eq. 72 and [1, Prop. 28]'s proof). At `Z(H)` the radius is half of that at `Z(½H)`, so at
`‖A‖_{p↦1} = 1` it is `1/2`, not `1`. Here `n = 2`, `m = 1`, `p = ∞` with `L = n - 1 = 1` as
[1, Lemma 26] sets it, and `A = e₁`: `‖A‖_{∞↦1} = 1`, while every point `(a, 0, -s)` of the
inbody, `|a|, |s| ≤ 1`, is `H β` for `β₁ = (a/2 - s/4, -s/4)`, `β₂ = (-a/2 - s/4, -s/4)`, of
supremum norm at most `3/4`; so `r ≤ 3/4 < 1`.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `A = e₁ ∈ ℝ^{2×1}`. -/
def aux_A27 : Mat ℝ 2 1 := fun i _ => if i = 0 then 1 else 0

theorem aux_mulVec (w : Fin 1 → ℝ) : aux_A27 *ᵥ w = ![w 0, 0] := by
  funext i
  fin_cases i <;> simp [aux_A27, mulVec, dotProduct]

/-- Every point of the inbody is `H β` with `‖β‖ ≤ 3/4`. -/
theorem aux_value_le (α : WithLp ∞ (PiLp ∞ (fun _ : Fin 1 => ℝ) × ℝ)) (hα : ‖α‖ ≤ 1) :
    coeffNorm (gadgetH 2) (gadgetGA ∞ aux_A27 1 α) ≤ 3 / 4 := by -- --- PROOF ---
  rw [WithLp.prod_norm_eq_sup, max_le_iff, Real.norm_eq_abs] at hα
  set a := α.fst 0
  set s := α.snd
  have ha : |a| ≤ 1 := (Real.norm_eq_abs a ▸ PiLp.norm_apply_le α.fst 0).trans hα.1
  have hs : |s| ≤ 1 := hα.2
  -- the preimage `β₁ = (a/2 - s/4, -s/4)`, `β₂ = (-a/2 - s/4, -s/4)`
  let β : Vec ℝ 2 × Vec ℝ 2 := (![a / 2 - s / 4, -s / 4], ![-a / 2 - s / 4, -s / 4])
  have hβ : gadgetH 2 β = gadgetGA ∞ aux_A27 1 α := by
    refine Prod.ext ?_ ?_
    · show β.1 - β.2 = aux_A27 *ᵥ WithLp.ofLp α.fst
      rw [aux_mulVec]
      funext i
      fin_cases i
      · simp [β, a]; ring
      · simp [β]
    · show ∑ i, β.1 i + ∑ i, β.2 i = -1 * α.snd
      simp [β, Fin.sum_univ_two, s]
      ring
  -- every entry of `β` is within `3/4`
  rw [← hβ]
  refine (coeffNorm_le _ β).trans ?_
  have h1 := abs_le.mp ha
  have h2 := abs_le.mp hs
  refine max_le ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_) <;>
    fin_cases i <;> simp only [β, Real.norm_eq_abs] <;> simp <;>
    refine abs_le.mpr ⟨by linarith, by linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `A = e₁`, `p = ∞`, `L = 1`: `‖A‖_{∞↦1} = 1`, yet `r(E_∞(G_A), Z(H))` exists and is at
most `3/4`, so not `1`. -/
theorem gadget_radius_iff_counterexample : -- --- CONCL ---
    IsGreatest ((fun v : PiLp ∞ (fun _ : Fin 1 => ℝ) => ∑ i, |(aux_A27 *ᵥ WithLp.ofLp v) i|) ''
        Metric.closedBall 0 1) 1 ∧
      ∃ r, IsGreatest ((fun α => coeffNorm (gadgetH 2) (gadgetGA ∞ aux_A27 1 α)) ''
        Metric.closedBall 0 1) r ∧ r ≤ 3 / 4 := by -- --- PROOF ---
  refine ⟨⟨⟨WithLp.toLp ∞ (fun _ => 1), ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, PiLp.norm_toLp]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp
  · simp [aux_mulVec]
  · rintro _ ⟨v, hv, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    simp only [aux_mulVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      abs_zero, add_zero]
    exact (Real.norm_eq_abs _ ▸ PiLp.norm_apply_le v 0).trans hv
  · -- the maximum exists: `½H` is onto, so `H` is, and the norm is continuous
    have hsurj : Function.Surjective (gadgetH 2) := fun x => by
      obtain ⟨β, hβ⟩ := (coeffNorm_half_gadgetH (n := 2) (by norm_num)).1 x
      exact ⟨(1 / 2 : ℝ) • β, by rw [map_smul]; exact hβ⟩
    obtain ⟨K, hK⟩ := exists_lipschitzWith_coeffNorm (gadgetH 2) hsurj
    have hcont : Continuous fun α => coeffNorm (gadgetH 2) (gadgetGA ∞ aux_A27 1 α) :=
      hK.continuous.comp (LinearMap.continuous_of_finiteDimensional _)
    obtain ⟨α₀, hα₀, hmax⟩ := (isCompact_closedBall
      (0 : WithLp ∞ (PiLp ∞ (fun _ : Fin 1 => ℝ) × ℝ)) 1).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩ hcont.continuousOn
    refine ⟨_, ⟨⟨α₀, hα₀, rfl⟩, fun _ ⟨α, hα, he⟩ => he ▸ hmax hα⟩, aux_value_le α₀ ?_⟩
    rwa [Metric.mem_closedBall, dist_zero_right] at hα₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
