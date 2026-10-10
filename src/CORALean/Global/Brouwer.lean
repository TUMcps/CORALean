import CORALean.Global.BrouwerClosedBall
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Brouwer's fixed-point theorem

A continuous map taking a nonempty compact convex subset `K` of a finite-dimensional real
normed space into itself has a fixed point in `K`.

`toEuclidean` carries `K` to an inner product space, where the nearest-point projection onto
`K` is continuous (it does not expand distances) and fixes `K`; `f` after it, rescaled into
the unit ball, is `exists_fixedPoint_closedBall`'s case, and its fixed point lies in `K`.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Metric


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A nonempty complete convex set is a continuous retract of an inner product space. -/
theorem aux_exists_retraction_convex {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E}
    (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) :
    ∃ P : E → E, Continuous P ∧ (∀ x, P x ∈ K) ∧ ∀ x ∈ K, P x = x := by -- --- PROOF ---
  have hex : ∀ x, ∃ v ∈ K, ∀ w ∈ K, inner ℝ (x - v) (w - v) ≤ 0 := fun x => by
    obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc hconv x
    exact ⟨v, hv, (norm_eq_iInf_iff_real_inner_le_zero hconv hv).mp hmin⟩
  choose P hPK hPvar using hex
  refine ⟨P, ?_, hPK, ?_⟩
  · -- the projection onto a convex set does not expand distances
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    have h1 := hPvar x (P y) (hPK y)
    have h2 := hPvar y (P x) (hPK x)
    have h3 : ‖P x - P y‖ ^ 2 ≤ inner ℝ (x - y) (P x - P y) := by
      rw [← real_inner_self_eq_norm_sq]
      have : inner ℝ (x - P x) (P y - P x) + inner ℝ (y - P y) (P x - P y)
          = inner ℝ (x - y) (P y - P x) + inner ℝ (P x - P y) (P x - P y) := by
        simp only [inner_sub_left, inner_sub_right, real_inner_comm]; ring
      have h5 : inner ℝ (x - y) (P y - P x) = - inner ℝ (x - y) (P x - P y) := by
        rw [← inner_neg_right, neg_sub]
      linarith
    have h4 := real_inner_le_norm (x - y) (P x - P y)
    -- so `‖P x - P y‖² ≤ ‖x - y‖ ‖P x - P y‖`
    by_cases hd : ‖P x - P y‖ = 0
    · rw [hd]; exact norm_nonneg _
    · have hpos : 0 < ‖P x - P y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
      nlinarith
  · -- on `K` the nearest point is the point itself
    intro x hx
    have h := hPvar x x hx
    rw [real_inner_self_eq_norm_sq] at h
    have : ‖x - P x‖ = 0 := by nlinarith [norm_nonneg (x - P x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm

/-- The theorem in an inner product space. -/
theorem aux_exists_fixedPoint_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) {f : E → E} (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by -- --- PROOF ---
  obtain ⟨P, hPc, hPK, hPid⟩ := aux_exists_retraction_convex hne hK.isComplete hconv
  -- `K` sits in a ball of radius `R`; rescale it to the unit ball
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : ∀ y ∈ K, ‖y‖ ≤ R := fun y hy =>
    (mem_closedBall_zero_iff.mp (hR₀ hy)).trans (le_max_left _ _)
  set F : E → E := fun z => R⁻¹ • f (P (R • z))
  have hFc : Continuous F := continuous_const.smul (hf.comp_continuous
    (hPc.comp (continuous_const.smul continuous_id)) fun z => hPK _)
  have hFB : ∀ z, ‖z‖ ≤ 1 → ‖F z‖ ≤ 1 := by
    intro z _
    simp only [F, norm_smul, norm_inv, Real.norm_of_nonneg hR.le]
    rw [inv_mul_le_iff₀ hR, mul_one]
    exact hKR _ (hfK (hPK _))
  -- a fixed point of the rescaled map is one of `f`, and lies in `K`
  obtain ⟨z, -, hz⟩ := exists_fixedPoint_closedBall hFc fun z hz =>
    mem_closedBall_zero_iff.mpr (hFB z (mem_closedBall_zero_iff.mp hz))
  have hRz : f (P (R • z)) = R • z := by
    have h := congrArg (R • ·) hz
    simpa only [F, smul_smul, mul_inv_cancel₀ hR.ne', one_smul] using h
  have hmem : R • z ∈ K := hRz ▸ hfK (hPK _)
  refine ⟨R • z, hmem, ?_⟩
  rwa [hPid _ hmem] at hRz


-- =======================================  MAIN THEOREM  ======================================= --

/-- Brouwer: a continuous self-map of a nonempty compact convex set in a finite-dimensional real
normed space has a fixed point. -/
theorem exists_fixedPoint_of_isCompact_convex {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {K : Set F} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) {f : F → F} (hf : ContinuousOn f K)
    (hfK : Set.MapsTo f K K) : ∃ x ∈ K, f x = x := by -- --- PROOF ---
  set e := toEuclidean (E := F)
  have hK' : IsCompact (e '' K) := hK.image e.continuous
  have hconv' : Convex ℝ (e '' K) := hconv.linear_image e.toLinearEquiv.toLinearMap
  have hmaps : Set.MapsTo e.symm (e '' K) K := by
    rintro _ ⟨x, hx, rfl⟩; rwa [e.symm_apply_apply]
  obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := aux_exists_fixedPoint_inner hK' hconv' (hne.image e)
    (f := fun y => e (f (e.symm y)))
    (e.continuous.comp_continuousOn (hf.comp e.symm.continuous.continuousOn hmaps))
    (fun y hy => ⟨f (e.symm y), hfK (hmaps hy), rfl⟩)
  refine ⟨x, hx, e.injective ?_⟩
  simpa using hy

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
