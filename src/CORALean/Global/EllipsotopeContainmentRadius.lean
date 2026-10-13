import CORALean.Global.CoeffNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The containment radius of two ellipsotopes

[1, Thm. 12]: for `Ê = E_p(G, c)` and `E = E_q(H, d)`,
`r = max_{‖α‖_p ≤ 1} min_{Hβ = Gα + c - d} ‖β‖_q` (Eq. 15) is the smallest scaling with
`Ê ⊆ r (E - d) + d`, and `r ≤ 1` iff `Ê ⊆ E`; where `rank [G, c - d, H] ≠ rank H` (Eq. 16),
that is `Im [G, c - d] ⊄ Im H`, no scaling works and `r = ∞` by convention. Any norms on
either coefficient space, `p`- and `q`-norms among them. A degenerate `E` needs no projection
(Eq. 19): where `Im [G, c - d] ⊆ Im H` the inner minimum is over a non-empty fibre, and
`coeffNorm` through `H` onto its range is Lipschitz, so the maximum is attained. The scalings
range over `ρ ≥ 0`, as in the proof: `E - d` is symmetric, so a negative `ρ` reaches the same
set as `|ρ|`, and among all reals there is no least.

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

variable {E₁ E₂ W : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup W] [NormedSpace ℝ W]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [FiniteDimensional ℝ E₂] in
/-- Through `H` onto its range the norm is the same. -/
theorem aux_coeffNorm_rangeRestrict (H : E₂ →ₗ[ℝ] W) (x : W) (hx : x ∈ LinearMap.range H) :
    coeffNorm H x = coeffNorm H.rangeRestrict ⟨x, hx⟩ := by -- --- PROOF ---
  unfold coeffNorm
  congr 2
  ext β
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

/-- The maximum of Eq. 15 is attained where the inbody's offsets lie in `Im H`. -/
theorem aux_exists_isGreatest (G : E₁ →ₗ[ℝ] W) (c : W) (H : E₂ →ₗ[ℝ] W) (d : W)
    (hmem : ∀ α, G α + c - d ∈ LinearMap.range H) :
    ∃ r, IsGreatest ((fun α => coeffNorm H (G α + c - d)) '' Metric.closedBall 0 1)
      r := by -- --- PROOF ---
  obtain ⟨K, hK⟩ := exists_lipschitzWith_coeffNorm H.rangeRestrict H.surjective_rangeRestrict
  have hg : Continuous fun α => (⟨G α + c - d, hmem α⟩ : LinearMap.range H) :=
    (((LinearMap.continuous_of_finiteDimensional G).add continuous_const).sub
      continuous_const).subtype_mk _
  have hcont : Continuous fun α => coeffNorm H (G α + c - d) := by
    have : (fun α => coeffNorm H (G α + c - d)) =
        fun α => coeffNorm H.rangeRestrict ⟨G α + c - d, hmem α⟩ :=
      funext fun α => aux_coeffNorm_rangeRestrict H _ (hmem α)
    rw [this]
    exact hK.continuous.comp hg
  obtain ⟨α₀, hα₀, hmax⟩ := (isCompact_closedBall (0 : E₁) 1).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩ hcont.continuousOn
  exact ⟨_, ⟨α₀, hα₀, rfl⟩, fun _ ⟨α, hα, he⟩ => he ▸ hmax hα⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ellipsotope_containmentRadius (G : E₁ →ₗ[ℝ] W) (c : W) (H : E₂ →ₗ[ℝ] W) (d : W) :
    let Ê := {x | ∃ α : E₁, ‖α‖ ≤ 1 ∧ x = c + G α}
    let E := {x | ∃ β : E₂, ‖β‖ ≤ 1 ∧ x = d + H β}
    (LinearMap.range G ≤ LinearMap.range H ∧ c - d ∈ LinearMap.range H →
      ∃ r, IsGreatest ((fun α => coeffNorm H (G α + c - d)) '' Metric.closedBall 0 1) r ∧
        IsLeast {ρ : ℝ | 0 ≤ ρ ∧ Ê ⊆ {y | ∃ x ∈ E, y = d + ρ • (x - d)}} r ∧
        (r ≤ 1 ↔ Ê ⊆ E)) ∧
      (¬(LinearMap.range G ≤ LinearMap.range H ∧ c - d ∈ LinearMap.range H) →
        ∀ ρ : ℝ, ¬ Ê ⊆ {y | ∃ x ∈ E, y = d + ρ • (x - d)}) := by -- --- PROOF ---
  intro Ê E
  refine ⟨fun ⟨hG, hcd⟩ => ?_, fun hn ρ hsub => hn ?_⟩
  · have hmem : ∀ α, G α + c - d ∈ LinearMap.range H := fun α => by
      rw [add_sub_assoc]
      exact add_mem (hG ⟨α, rfl⟩) hcd
    obtain ⟨r, hr⟩ := aux_exists_isGreatest G c H d hmem
    -- every point `c + Gα` is `d + Hβ` with `‖β‖ ≤ r`
    have hpt : ∀ α : E₁, ‖α‖ ≤ 1 → ∃ β, H β = G α + c - d ∧ ‖β‖ ≤ r := fun α hα => by
      obtain ⟨β, hβ⟩ := hmem α
      exact (coeffNorm_le_iff H ⟨β, hβ⟩).mp
        (hr.2 ⟨α, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩)
    have hr0 : 0 ≤ r := by
      obtain ⟨α, -, he⟩ := hr.1
      rw [← he]; exact coeffNorm_nonneg _ _
    -- `r` is a scaling that works
    have hmemr : r ∈ {ρ : ℝ | 0 ≤ ρ ∧ Ê ⊆ {y | ∃ x ∈ E, y = d + ρ • (x - d)}} := by
      refine ⟨hr0, ?_⟩
      rintro _ ⟨α, hα, rfl⟩
      obtain ⟨β, hβ, hβr⟩ := hpt α hα
      rcases hr0.lt_or_eq with hpos | hzero
      · refine ⟨d + H (r⁻¹ • β), ⟨r⁻¹ • β, ?_, rfl⟩, ?_⟩
        · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos]
          exact inv_mul_le_one_of_le₀ hβr hpos.le
        · rw [add_sub_cancel_left, map_smul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, hβ]
          abel
      · rw [← hzero] at hβr
        have hβ0 : β = 0 := norm_le_zero_iff.mp hβr
        rw [hβ0, map_zero] at hβ
        refine ⟨d + H 0, ⟨0, by simp, rfl⟩, ?_⟩
        rw [← hzero, zero_smul, add_zero]
        rw [eq_comm, sub_eq_zero] at hβ
        rw [← hβ]; abel
    -- and no smaller one does: the maximizer's point needs `ρ ≥ r`
    have hleast : ∀ ρ ∈ {ρ : ℝ | 0 ≤ ρ ∧ Ê ⊆ {y | ∃ x ∈ E, y = d + ρ • (x - d)}}, r ≤ ρ := by
      rintro ρ ⟨hρ0, hsub⟩
      obtain ⟨α, hα, he⟩ := hr.1
      rw [Metric.mem_closedBall, dist_zero_right] at hα
      obtain ⟨_, ⟨β, hβ, rfl⟩, hx⟩ := hsub ⟨α, hα, rfl⟩
      have : H (ρ • β) = G α + c - d := by
        rw [map_smul]
        rw [add_sub_cancel_left] at hx
        rw [show G α + c - d = c + G α - d by abel, hx]
        abel
      rw [← he]
      refine (this ▸ coeffNorm_le H (ρ • β)).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ0]
      exact mul_le_of_le_one_right hρ0 hβ
    -- `r ≤ 1` is containment: `1` is a scaling exactly when `Ê ⊆ E`
    refine ⟨r, hr, ⟨hmemr, hleast⟩, ⟨fun h1 => ?_, fun hsub => hleast 1 ⟨zero_le_one, ?_⟩⟩⟩
    · rintro _ ⟨α, hα, rfl⟩
      obtain ⟨β, hβ, hβr⟩ := hpt α hα
      show ∃ β : E₂, ‖β‖ ≤ 1 ∧ c + G α = d + H β
      exact ⟨β, hβr.trans h1, by rw [hβ]; abel⟩
    · intro y hy
      exact ⟨y, hsub hy, by rw [one_smul]; abel⟩
  · -- every scaled point lies in `d + Im H`, so the inbody's offsets do
    have hoff : ∀ α : E₁, ‖α‖ ≤ 1 → c + G α - d ∈ LinearMap.range H := fun α hα => by
      obtain ⟨_, ⟨β, -, rfl⟩, hx⟩ := hsub ⟨α, hα, rfl⟩
      rw [hx, add_sub_cancel_left, add_sub_cancel_left]
      exact ⟨ρ • β, map_smul H ρ β⟩
    have hcd : c - d ∈ LinearMap.range H := by
      simpa using hoff 0 (by simp)
    refine ⟨?_, hcd⟩
    rintro _ ⟨α', rfl⟩
    rcases eq_or_ne α' 0 with rfl | hα'
    · simp
    -- a nonzero coefficient, scaled into the ball
    have hpos : 0 < ‖α'‖ := norm_pos_iff.mpr hα'
    have h := hoff (‖α'‖⁻¹ • α') (by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne'])
    have hGα : G (‖α'‖⁻¹ • α') ∈ LinearMap.range H := by
      have := sub_mem h hcd
      rwa [show c + G (‖α'‖⁻¹ • α') - d - (c - d) = G (‖α'‖⁻¹ • α') by abel] at this
    have := Submodule.smul_mem _ ‖α'‖ hGα
    rwa [← map_smul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
