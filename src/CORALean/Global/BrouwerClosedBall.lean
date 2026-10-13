module

public import CORALean.Global.NoRetractionClosedBall
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

/-!
# Brouwer's fixed-point theorem on the closed unit ball

A continuous self-map of the closed unit ball of a finite-dimensional real inner product
space has a fixed point.

First for a `C¹` map `g` without one: the point where the ray from `g x` through `x` leaves
the ball, `x + σ(x)(x - g x)` with `σ` the larger root of a quadratic, is a `C¹` retraction
of an open neighbourhood of the ball onto the sphere, which `no_contDiff_retraction_closedBall`
rules out. Then for a continuous `f`: a smooth map uniformly within `η` of `f` (Mathlib's
smooth partitions of unity), shrunk by `1 + η` to map the ball into itself, has a fixed point,
and if `f` moved every point by at least `ε` it could not for `η = ε / 4`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Metric
open scoped Manifold ContDiff


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The `C¹` case: a `C¹` self-map of the closed unit ball has a fixed point. -/
theorem aux_exists_fixedPoint_of_contDiff {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → E} (hg : ContDiff ℝ 1 g)
    (hgB : ∀ x, ‖x‖ ≤ 1 → ‖g x‖ ≤ 1) : ∃ x, ‖x‖ ≤ 1 ∧ g x = x := by -- --- PROOF ---
  by_contra hno
  simp only [not_exists, not_and] at hno
  -- where the ray from `g x` through `x` leaves the ball: `σ` the larger root of `a σ² + 2bσ + c`
  set u : E → E := fun x => x - g x
  set a : E → ℝ := fun x => ‖u x‖ ^ 2
  set b : E → ℝ := fun x => inner ℝ x (u x)
  set c : E → ℝ := fun x => ‖x‖ ^ 2 - 1
  set D : E → ℝ := fun x => b x ^ 2 - a x * c x
  set U : Set E := {x | u x ≠ 0} ∩ {x | 0 < D x}
  set σ : E → ℝ := fun x => (-(b x) + Real.sqrt (D x)) / a x
  set r : E → E := fun x => x + σ x • u x
  -- the coefficients are `C¹`, and `U`, where `u ≠ 0` and `D > 0`, is open
  have hu : ContDiff ℝ 1 u := contDiff_id.sub hg
  have ha : ContDiff ℝ 1 a := hu.norm_sq ℝ
  have hb : ContDiff ℝ 1 b := contDiff_id.inner ℝ hu
  have hc : ContDiff ℝ 1 c := (contDiff_norm_sq ℝ).sub contDiff_const
  have hD : ContDiff ℝ 1 D := (hb.pow 2).sub (ha.mul hc)
  have hUo : IsOpen U :=
    (isOpen_ne_fun hu.continuous continuous_const).inter (isOpen_lt continuous_const hD.continuous)
  have ha0 : ∀ x ∈ U, a x ≠ 0 := fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx.1)
  have hbx : ∀ x, b x = ‖x‖ ^ 2 - inner ℝ x (g x) := fun x => by
    simp only [b, u, inner_sub_right, real_inner_self_eq_norm_sq]
  -- the ball lies in `U`: a point where the discriminant vanishes would be fixed
  have hBU : closedBall (0 : E) 1 ⊆ U := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx
    have hux : u x ≠ 0 := sub_ne_zero.mpr fun h => hno x hx h.symm
    refine ⟨hux, ?_⟩
    have hapos : 0 < a x := by positivity
    have hcx : c x ≤ 0 := by
      simp only [c]; nlinarith [norm_nonneg x]
    by_contra hDle
    -- `D ≤ 0` forces `b = 0` and `‖x‖ = 1`, so `⟪x, g x⟫ = 1` and `g x = x`
    have hDle' : D x ≤ 0 := not_lt.mp hDle
    have hb0 : b x = 0 := by
      simp only [D] at hDle'
      nlinarith [sq_nonneg (b x), mul_nonpos_of_nonneg_of_nonpos hapos.le hcx]
    have hc0 : c x = 0 := by
      simp only [D] at hDle'
      rw [hb0] at hDle'
      have := mul_nonpos_of_nonneg_of_nonpos hapos.le hcx
      nlinarith
    have hx1 : ‖x‖ ^ 2 = 1 := by simp only [c] at hc0; linarith
    have hin : inner ℝ x (g x) = 1 := by rw [hbx] at hb0; linarith
    have hg1 := hgB x hx
    have : ‖u x‖ ^ 2 ≤ 0 := by
      simp only [u]
      rw [norm_sub_sq_real, hx1, hin]
      nlinarith [norm_nonneg (g x)]
    exact hux (norm_eq_zero.mp (by nlinarith [norm_nonneg (u x)]))
  -- on `U`, `σ` and so `r` are `C¹`
  have hσ : ContDiffOn ℝ 1 σ U :=
    (hb.neg.contDiffOn.add (hD.contDiffOn.sqrt fun x hx => hx.2.ne')).div ha.contDiffOn ha0
  have hr : ContDiffOn ℝ 1 r U := contDiffOn_id.add (hσ.smul hu.contDiffOn)
  -- `σ` solves `a σ² + 2 b σ + c = 0`, so `r` lands on the sphere
  have hnorm : ∀ x ∈ U, ‖r x‖ = 1 := by
    intro x hx
    have hS : Real.sqrt (D x) ^ 2 = D x := Real.sq_sqrt hx.2.le
    have hσa : σ x * a x = -(b x) + Real.sqrt (D x) := div_mul_cancel₀ _ (ha0 x hx)
    have hsq : ‖r x‖ ^ 2 = 1 := by
      have h1 : ‖r x‖ ^ 2 = ‖x‖ ^ 2 + 2 * σ x * b x + σ x ^ 2 * a x := by
        simp only [r, a, b]
        rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        ring
      have h2 : a x * (c x + 2 * σ x * b x + σ x ^ 2 * a x) = 0 := by
        have hDdef : D x = b x ^ 2 - a x * c x := rfl
        linear_combination (2 * b x + σ x * a x - b x + Real.sqrt (D x)) * hσa + hS - hDdef
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h (ha0 x hx)
      · rw [h1]; simp only [c] at h; linarith
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_one] at this
  -- on the sphere `σ = 0`
  have hfix : ∀ x, ‖x‖ = 1 → r x = x := by
    intro x hx
    have hb0 : 0 ≤ b x := by
      rw [hbx, hx]
      have := real_inner_le_norm x (g x)
      rw [hx, one_mul] at this
      nlinarith [hgB x hx.le]
    have hσ0 : σ x = 0 := by
      have hDx : D x = b x ^ 2 := by simp only [D, c, hx]; ring
      simp only [σ, hDx, Real.sqrt_sq hb0, neg_add_cancel, zero_div]
    simp only [r, hσ0, zero_smul, add_zero]
  exact no_contDiff_retraction_closedBall hUo hBU hr hnorm hfix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Brouwer: a continuous map taking the closed unit ball into itself has a fixed point there. -/
theorem exists_fixedPoint_closedBall {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} (hf : Continuous f)
    (hfB' : Set.MapsTo f (closedBall (0 : E) 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : E) 1, f x = x := by -- --- PROOF ---
  have hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1 := fun x hx =>
    mem_closedBall_zero_iff.mp (hfB' (mem_closedBall_zero_iff.mpr hx))
  by_contra hno
  simp only [mem_closedBall_zero_iff] at hno
  simp only [not_exists, not_and] at hno
  -- the least displacement on the ball
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_closedBall (0 : E) 1).exists_isMinOn
    ⟨0, mem_closedBall_self zero_le_one⟩ (hf.sub continuous_id).norm.continuousOn
  set ε := ‖f x₀ - x₀‖
  have hε : 0 < ε := norm_pos_iff.mpr (sub_ne_zero.mpr (hno x₀ (mem_closedBall_zero_iff.mp hx₀)))
  set η := ε / 4
  have hη : 0 < η := by positivity
  -- a smooth map within `η` of `f` everywhere
  obtain ⟨p, hp⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const 𝓘(ℝ, E)
    (n := 1) (t := fun x => ball (f x) η) (fun x => convex_ball _ _)
    (fun x => ⟨f x, (hf.continuousAt.eventually (ball_mem_nhds (f x) hη)).mono
      fun y hy => by rw [mem_ball, dist_comm]; exact hy⟩)
  have hpd : ContDiff ℝ 1 p := contMDiff_iff_contDiff.mp p.contMDiff
  set g : E → E := fun x => (1 + η)⁻¹ • p x
  have hg : ContDiff ℝ 1 g := contDiff_const.smul hpd
  have hpf : ∀ x, ‖p x - f x‖ < η := fun x => by
    have := hp x; rwa [mem_ball, dist_eq_norm] at this
  have hgB : ∀ x, ‖x‖ ≤ 1 → ‖g x‖ ≤ 1 := by
    intro x hx
    simp only [g, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 + η)]
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    calc ‖p x‖ = ‖(p x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖p x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ η + 1 := add_le_add (hpf x).le (hfB x hx)
      _ = 1 + η := add_comm _ _
  obtain ⟨x, hx, hgx⟩ := aux_exists_fixedPoint_of_contDiff hg hgB
  -- but `g` moves every point of the ball
  have hgf : ‖g x - f x‖ < 2 * η := by
    have : g x - f x = (1 + η)⁻¹ • ((p x - f x) - η • f x) := by
      simp only [g, smul_sub, smul_smul]
      rw [show (1 + η)⁻¹ • f x = f x - ((1 + η)⁻¹ * η) • f x by
        rw [show f x - ((1 + η)⁻¹ * η) • f x = (1 - (1 + η)⁻¹ * η) • f x by
          rw [sub_smul, one_smul]]
        congr 1; field_simp; ring]
      abel
    rw [this, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 + η),
      inv_mul_lt_iff₀ (by positivity)]
    calc ‖p x - f x - η • f x‖ ≤ ‖p x - f x‖ + ‖η • f x‖ := norm_sub_le _ _
      _ < η + η * 1 := by
        rw [norm_smul, Real.norm_of_nonneg hη.le]
        exact add_lt_add_of_lt_of_le (hpf x) (mul_le_mul_of_nonneg_left (hfB x hx) hη.le)
      _ ≤ (1 + η) * (2 * η) := by nlinarith
  -- yet `f` moves `x` by at least `ε`
  have hle : ε ≤ ‖f x - x‖ := hmin (mem_closedBall_zero_iff.mpr hx)
  have : ‖f x - x‖ < ε := by
    calc ‖f x - x‖ = ‖f x - g x‖ := by rw [hgx]
      _ = ‖g x - f x‖ := norm_sub_rev _ _
      _ < 2 * η := hgf
      _ < ε := by simp only [η]; linarith
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
