module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.EMetricSpace.Lipschitz

@[expose] public section

/-!
# The norm a coefficient ball induces through a linear map

`coeffNorm G x = min {‖α‖ | G α = x}`: how far the coefficient ball must be scaled for its
image under `G` to reach `x`. At `G` a zonotope's generator map and the supremum norm it is
the zonotope norm of Kulmburg and Althoff; at a `p`-norm it is an ellipsotope's. Nothing
about the coefficient norm is used beyond its being a norm on a finite-dimensional space,
which is what makes the minimum attained: the fibre is a closed affine subspace, and a
bounded piece of it is compact.

Off `range G` the infimum is over `∅`, and reads `0`; every statement here that needs a
preimage asks for one, and at a surjective `G` that is every point. That this is a norm
there is `[1, Thm. 1]`, and at any coefficient norm `[2, Prop. 2.2]`.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
* [2] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup V] [Module ℝ V]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `min {‖α‖ | G α = x}`, `0` where nothing maps to `x`. -/
noncomputable def coeffNorm (G : E →ₗ[ℝ] V) (x : V) : ℝ := sInf (norm '' {α | G α = x})

theorem coeffNorm_nonneg (G : E →ₗ[ℝ] V) (x : V) : 0 ≤ coeffNorm G x :=
  Real.sInf_nonneg (by rintro _ ⟨α, -, rfl⟩; exact norm_nonneg α)

theorem coeffNorm_le (G : E →ₗ[ℝ] V) (α : E) : coeffNorm G (G α) ≤ ‖α‖ :=
  csInf_le ⟨0, by rintro _ ⟨_, -, rfl⟩; exact norm_nonneg _⟩ ⟨α, rfl, rfl⟩

/-- The minimum is attained: the fibre is closed, and cut down to a ball it is compact. -/
theorem exists_coeffNorm_eq [FiniteDimensional ℝ E] (G : E →ₗ[ℝ] V) {x : V}
    (hx : ∃ α, G α = x) : ∃ α, G α = x ∧ ‖α‖ = coeffNorm G x := by -- --- PROOF ---
  obtain ⟨α₀, hα₀⟩ := hx
  -- the fibre is `α₀ + ker G`, a closed set
  have hfib : {α | G α = x} = (fun β => α₀ + β) '' (LinearMap.ker G : Set E) := by
    ext α
    constructor
    · intro h
      refine ⟨α - α₀, ?_, add_sub_cancel α₀ α⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hα₀]
      exact sub_eq_zero.mpr h
    · rintro ⟨β, hβ, rfl⟩
      simpa [map_add, LinearMap.mem_ker.mp hβ] using hα₀
  have hclosed : IsClosed {α | G α = x} := by
    rw [hfib]
    exact (Homeomorph.addLeft α₀).isClosedMap _ (Submodule.closed_of_finiteDimensional _)
  let K := {α | G α = x} ∩ Metric.closedBall 0 ‖α₀‖
  have hK : IsCompact K := (isCompact_closedBall 0 ‖α₀‖).inter_left hclosed
  obtain ⟨α, ⟨hαx, -⟩, hmin⟩ := hK.exists_isMinOn ⟨α₀, hα₀, by simp⟩ continuous_norm.continuousOn
  -- the minimizer over the ball wins over the whole fibre: beyond the ball points are longer
  have hall : ∀ β, G β = x → ‖α‖ ≤ ‖β‖ := by
    intro β hβ
    by_cases hb : ‖β‖ ≤ ‖α₀‖
    · exact hmin ⟨hβ, by simpa using hb⟩
    · exact (hmin ⟨hα₀, by simp⟩).trans (le_of_not_ge hb)
  refine ⟨α, hαx, le_antisymm ?_ (hαx ▸ coeffNorm_le G α)⟩
  exact le_csInf ⟨_, α₀, hα₀, rfl⟩ (by rintro _ ⟨β, hβ, rfl⟩; exact hall β hβ)

theorem coeffNorm_le_iff [FiniteDimensional ℝ E] (G : E →ₗ[ℝ] V) {x : V} (hx : ∃ α, G α = x)
    {r : ℝ} : coeffNorm G x ≤ r ↔ ∃ α, G α = x ∧ ‖α‖ ≤ r := by -- --- PROOF ---
  constructor
  · intro h
    obtain ⟨α, hα, he⟩ := exists_coeffNorm_eq G hx
    exact ⟨α, hα, he ▸ h⟩
  · rintro ⟨α, rfl, hα⟩
    exact (coeffNorm_le G α).trans hα

theorem coeffNorm_zero (G : E →ₗ[ℝ] V) : coeffNorm G 0 = 0 :=
  le_antisymm (by simpa using coeffNorm_le G 0) (coeffNorm_nonneg G 0)

theorem coeffNorm_add_le [FiniteDimensional ℝ E] (G : E →ₗ[ℝ] V) {x y : V}
    (hx : ∃ α, G α = x) (hy : ∃ α, G α = y) :
    coeffNorm G (x + y) ≤ coeffNorm G x + coeffNorm G y := by
  obtain ⟨α, rfl, hα⟩ := exists_coeffNorm_eq G hx
  obtain ⟨β, rfl, hβ⟩ := exists_coeffNorm_eq G hy
  rw [← hα, ← hβ, ← map_add]
  exact (coeffNorm_le G _).trans (norm_add_le α β)

theorem coeffNorm_smul [FiniteDimensional ℝ E] (G : E →ₗ[ℝ] V) {x : V} (hx : ∃ α, G α = x)
    (a : ℝ) : coeffNorm G (a • x) = |a| * coeffNorm G x := by -- --- PROOF ---
  obtain ⟨α, rfl, hα⟩ := exists_coeffNorm_eq G hx
  rcases eq_or_ne a 0 with rfl | ha
  · simp [coeffNorm_zero]
  refine le_antisymm ?_ ?_
  · rw [← map_smul, ← hα, ← Real.norm_eq_abs, ← norm_smul]
    exact coeffNorm_le G _
  -- the other way, divide back by `a`
  · obtain ⟨β, hβ, hβn⟩ := exists_coeffNorm_eq G ⟨a • α, rfl⟩
    -- a minimizer for `a x`, divided by `a`, reaches `x`
    have hle : coeffNorm G (G α) ≤ |a|⁻¹ * ‖β‖ := by
      have : G (a⁻¹ • β) = G α := by rw [map_smul, hβ, map_smul, smul_smul, inv_mul_cancel₀ ha,
        one_smul]
      rw [← this, ← abs_inv, ← Real.norm_eq_abs, ← norm_smul]
      exact coeffNorm_le G _
    rw [hβn] at hle
    have hpos : 0 < |a| := abs_pos.mpr ha
    rw [← map_smul]
    calc |a| * coeffNorm G (G α) ≤ |a| * (|a|⁻¹ * coeffNorm G (G (a • α))) :=
          mul_le_mul_of_nonneg_left hle hpos.le
      _ = coeffNorm G (G (a • α)) := by field_simp

theorem coeffNorm_eq_zero_iff [FiniteDimensional ℝ E] (G : E →ₗ[ℝ] V) {x : V}
    (hx : ∃ α, G α = x) : coeffNorm G x = 0 ↔ x = 0 := by -- --- PROOF ---
  constructor
  · intro h
    obtain ⟨α, rfl, hα⟩ := exists_coeffNorm_eq G hx
    rw [h, norm_eq_zero] at hα
    rw [hα, map_zero]
  · rintro rfl
    exact coeffNorm_zero G

/-- Through a surjective map the norm is bounded by a multiple of any norm on the target:
a linear right inverse is continuous in finite dimension. -/
theorem exists_coeffNorm_le_mul_norm [FiniteDimensional ℝ E] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] (G : E →ₗ[ℝ] W) (hG : Function.Surjective G) :
    ∃ C, 0 ≤ C ∧ ∀ x, coeffNorm G x ≤ C * ‖x‖ := by -- --- PROOF ---
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective G (LinearMap.range_eq_top.mpr hG)
  refine ⟨‖LinearMap.toContinuousLinearMap R‖, norm_nonneg _, fun x => ?_⟩
  have hx : G (R x) = x := by simpa using congrArg (fun f => f x) hR
  calc coeffNorm G x = coeffNorm G (G (R x)) := by rw [hx]
    _ ≤ ‖R x‖ := coeffNorm_le G _
    _ ≤ _ := (LinearMap.toContinuousLinearMap R).le_opNorm x

/-- And so it is Lipschitz: `ν x ≤ ν y + ν (x - y) ≤ ν y + C ‖x - y‖`. -/
theorem exists_lipschitzWith_coeffNorm [FiniteDimensional ℝ E] {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] (G : E →ₗ[ℝ] W) (hG : Function.Surjective G) :
    ∃ K : NNReal, LipschitzWith K (coeffNorm G) := by -- --- PROOF ---
  obtain ⟨C, hC0, hC⟩ := exists_coeffNorm_le_mul_norm G hG
  refine ⟨Real.toNNReal C, LipschitzWith.of_le_add_mul _ fun x y => ?_⟩
  have h := coeffNorm_add_le G (hG y) (hG (x - y))
  rw [add_sub_cancel] at h
  have := hC (x - y)
  rw [dist_eq_norm, Real.coe_toNNReal C hC0]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
