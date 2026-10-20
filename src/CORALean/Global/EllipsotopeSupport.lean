module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# The support function of an ellipsotope

`[1, Eq. 19]`: `max_{x ∈ E_p(G, c)} zᵀ x = ‖Gᵀ z‖_{p*} + zᵀ c`. The dual norm
`‖Gᵀ z‖_{p*}` is, by `[1, Eq. 1]`, `sup_{‖α‖_p ≤ 1} zᵀ G α`, the operator norm of
`z ∘ G`; so the identity is that a functional attains its norm on the closed unit ball,
which in finite dimension is compact (`isGreatest_apply_closedBall`). Any norm on the
coefficients.

## Inputs
* `G` – generator map
* `c` – center
* `z` – direction functional

## Hypotheses
* none

## Conclusion
* the functional's maximum is its dual norm on the generators plus its center value

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A functional attains its norm on the closed unit ball. -/
theorem isGreatest_apply_closedBall (f : E →L[ℝ] ℝ) :
    IsGreatest (f '' Metric.closedBall 0 1) ‖f‖ := by -- --- PROOF ---
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩ f.continuous.continuousOn
  have hle : ∀ x ∈ Metric.closedBall (0 : E) 1, f x ≤ ‖f‖ := fun x hx =>
    (le_abs_self _).trans ((f.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg f)
      (by simpa using hx)))
  -- the maximum bounds `|f x| / ‖x‖`, so the norm
  have hge : ‖f‖ ≤ f x₀ := by
    have hm0 : 0 ≤ f x₀ := by simpa using hmax (Metric.mem_closedBall_self zero_le_one)
    refine f.opNorm_le_bound hm0 fun x => ?_
    -- at `x ≠ 0`, test `±x / ‖x‖`
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hu : ∀ s : ℝ, |s| = 1 → (s * ‖x‖⁻¹) • x ∈ Metric.closedBall (0 : E) 1 := by
      intro s hs
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_mul, hs,
        one_mul, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
    have h1 := hmax (hu 1 (by simp))
    have h2 := hmax (hu (-1) (by simp))
    simp only [Set.mem_setOf_eq, map_smul, smul_eq_mul] at h1 h2
    have h1' : ‖x‖⁻¹ * f x ≤ f x₀ := by linarith
    have h2' : ‖x‖⁻¹ * -f x ≤ f x₀ := by linarith
    rw [inv_mul_le_iff₀ hn] at h1' h2'
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  exact ⟨⟨x₀, hx₀, le_antisymm (hle x₀ hx₀) hge⟩, by rintro _ ⟨x, hx, rfl⟩; exact hle x hx⟩

variable [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Eq. 19]`: `max_{x ∈ E_p(G, c)} z x = ‖z ∘ G‖ + z c`. -/
theorem isGreatest_support_ellipsotope (G : E →ₗ[ℝ] V) (c : V) (z : V →L[ℝ] ℝ) :
    IsGreatest ((fun x => z x) '' {x | ∃ α : E, ‖α‖ ≤ 1 ∧ x = c + G α})
      (‖z.comp (LinearMap.toContinuousLinearMap G)‖ + z c) := by -- --- PROOF ---
  obtain ⟨⟨α₀, hα₀, he⟩, hub⟩ :=
    isGreatest_apply_closedBall (z.comp (LinearMap.toContinuousLinearMap G))
  refine ⟨⟨c + G α₀, ⟨α₀, by simpa using hα₀, rfl⟩, ?_⟩, ?_⟩
  · simp only [map_add]
    rw [← he]
    simp [add_comm]
  -- every point is `c + G α`, and `z (G α)` is at most the norm
  · rintro _ ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    simp only [map_add]
    have := hub ⟨α, by simpa using hα, rfl⟩
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_toContinuousLinearMap'] at this
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
