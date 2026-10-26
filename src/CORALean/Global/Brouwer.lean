module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

/-!
# Brouwer's fixed-point theorem

A continuous map taking a nonempty compact convex subset `K` of a finite-dimensional real
normed space into itself has a fixed point in `K`.

`toEuclidean` carries `K` to an inner product space, where the nearest-point projection onto
`K` is continuous (it does not expand distances) and fixes `K`; `f` after it, rescaled into
the unit ball, is `aux_exists_fixedPoint_closedBall`'s case, and its fixed point lies in `K`.

## Inputs
* `F` – finite-dimensional real normed space
* `K` – compact convex set
* `f` – self-map of the set

## Hypotheses
* `hK` – the set is compact
* `hconv` – the set is convex
* `hne` – the set is nonempty
* `hf` – `f` is continuous on the set
* `hfK` – `f` maps the set into itself

## Conclusion
* `f` has a fixed point in the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Metric


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open scoped Manifold ContDiff
open Polynomial MeasureTheory

/-- `det (1 + A)` from `det (1 + v j • A)` at `finrank + 1` distinct nodes, by Lagrange. -/
private theorem aux_det_eval_one {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {v : ℕ → ℝ} (hv : Set.InjOn v (Finset.range (Module.finrank ℝ E + 1)))
    (A : E →L[ℝ] E) : -- --- CONCL ---
    (ContinuousLinearMap.id ℝ E + (1 : ℝ) • A).det =
      ∑ j ∈ Finset.range (Module.finrank ℝ E + 1),
        (ContinuousLinearMap.id ℝ E + v j • A).det *
          (Lagrange.basis (Finset.range (Module.finrank ℝ E + 1)) v j).eval 1 := by -- --- PROOF ---
  set s := Finset.range (Module.finrank ℝ E + 1)
  let b := Module.finBasis ℝ E
  let M := LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)
  let P : ℝ[X] := Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin (Module.finrank ℝ E))
    (Fin (Module.finrank ℝ E)) ℝ).map C)
  -- the determinant along the ray `t ↦ id + t • A` is `P` evaluated at `t`
  have hP : ∀ t : ℝ, (ContinuousLinearMap.id ℝ E + t • A).det = P.eval t := by
    intro t
    have h1 : ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = LinearMap.id + t • (A : E →ₗ[ℝ] E) := rfl
    rw [ContinuousLinearMap.det, h1, ← LinearMap.det_toMatrix b, map_add, map_smul,
      LinearMap.toMatrix_id]
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [M, Matrix.one_apply, add_comm]
    split_ifs <;> simp only [eval_one, eval_zero] <;> ring
  -- of degree at most the dimension, so the nodes determine it
  have hdeg : P.degree < s.card := by
    rw [Finset.card_range]
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    have := natDegree_det_X_add_C_le M (1 : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ)
    rw [Fintype.card_fin] at this
    exact_mod_cast Nat.lt_succ_of_le this
  have hI := Lagrange.eq_interpolate hv hdeg
  rw [hP, hI, Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, hP]


/-- A derivative of a map into the unit sphere is singular. -/
private theorem aux_det_eq_zero {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {r : E → E} {r' : E →L[ℝ] E} {x : E} (hr : HasFDerivAt r r' x)
    (hn : ∀ᶠ y in nhds x, ‖r y‖ = 1) : -- --- CONCL ---
    r'.det = 0 := by -- --- PROOF ---
  have h1 : HasFDerivAt (fun y => ‖r y‖ ^ 2) (2 • (innerSL ℝ (r x)).comp r') x := hr.norm_sq
  have h2 : HasFDerivAt (fun y => ‖r y‖ ^ 2) (0 : E →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq (hn.mono fun y hy => by simp [hy])
  have h3 := h1.unique h2
  have hperp : ∀ w, inner ℝ (r x) (r' w) = 0 := by
    intro w
    have := congrArg (fun L => L w) h3
    simpa using this
  by_contra hdet
  have hu : IsUnit (r' : E →ₗ[ℝ] E) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨w, hw⟩ := ((Module.End.isUnit_iff _).mp hu).2 (r x)
  have h4 := hperp w
  have hrx : ‖r x‖ = 1 := hn.self_of_nhds
  change inner ℝ (r x) ((r' : E →ₗ[ℝ] E) w) = 0 at h4
  rw [hw, real_inner_self_eq_norm_sq, hrx] at h4
  norm_num at h4


/-- `1 + t A` has a positive determinant while `t ‖A‖ < 1`. -/
private theorem aux_det_pos {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →L[ℝ] E) {C : ℝ} (hA : ‖A‖ ≤ C) {t : ℝ} (ht0 : 0 ≤ t)
    (htC : t * C < 1) : -- --- CONCL ---
    0 < (ContinuousLinearMap.id ℝ E + t • A).det := by -- --- PROOF ---
  set φ : ℝ → ℝ := fun s => (ContinuousLinearMap.id ℝ E + s • A).det
  have hφc : Continuous φ :=
    ContinuousLinearMap.continuous_det.comp (continuous_const.add
      (continuous_id.smul continuous_const))
  have hφ0 : φ 0 = 1 := by
    simp only [φ, zero_smul, add_zero]
    exact LinearMap.det_id
  -- on `[0, t]`, `1 + s A` is injective, so its determinant never vanishes
  have hne : ∀ s ∈ Set.Icc 0 t, φ s ≠ 0 := by
    intro s hs hdet
    have hnu : ¬ IsUnit ((ContinuousLinearMap.id ℝ E + s • A : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
      rw [LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]; exact hdet
    rw [Module.End.isUnit_iff] at hnu
    apply hnu
    -- `w = -s A w` forces `w = 0`, as `s ‖A‖ < 1`
    have hinj' : Function.Injective
        ((ContinuousLinearMap.id ℝ E + s • A : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      change w + s • A w = 0 at hw
      have hw' : w = -(s • A w) := eq_neg_of_add_eq_zero_left hw
      have hle : ‖w‖ ≤ s * C * ‖w‖ := by
        calc ‖w‖ = s * ‖A w‖ := by
              rw [congrArg norm hw', norm_neg, norm_smul, Real.norm_of_nonneg hs.1]
          _ ≤ s * (C * ‖w‖) := mul_le_mul_of_nonneg_left
              (A.le_opNorm w |>.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) hs.1
          _ = s * C * ‖w‖ := by ring
      have hC0 : 0 ≤ C := (norm_nonneg A).trans hA
      have hsC : s * C < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hs.2 hC0) htC
      by_contra hw0
      have : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      nlinarith
    exact ⟨hinj', LinearMap.injective_iff_surjective.mp hinj'⟩
  -- so it keeps the sign it has at `s = 0`
  by_contra hle
  replace hle := not_lt.mp hle
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht0 hφc.continuousOn
    ⟨hle, by rw [hφ0]; norm_num⟩
  exact hne s hs hs0


/-- A map `C`-Lipschitz on the closed unit ball and zero on its sphere, extended by zero, is
`C`-Lipschitz everywhere (given a unit vector `u`). -/
private theorem aux_norm_extension_sub_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : E → E) {C : NNReal} (hLip : LipschitzOnWith C h (closedBall 0 1))
    (hsph : ∀ x : E, ‖x‖ = 1 → h x = 0) {u : E} (hu : ‖u‖ = 1) (x y : E) : -- --- CONCL ---
    ‖(if ‖x‖ ≤ 1 then h x else 0) - (if ‖y‖ ≤ 1 then h y else 0)‖ ≤
      C * ‖x - y‖ := by -- --- PROOF ---
  set B := closedBall (0 : E) 1
  -- `h` is at most `C` times the distance to the sphere
  have hbd : ∀ x ∈ B, ‖h x‖ ≤ C * (1 - ‖x‖) := by
    intro x hx
    have hxle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    obtain ⟨z, hz1, hxz⟩ : ∃ z : E, ‖z‖ = 1 ∧ ‖x - z‖ = 1 - ‖x‖ := by
      by_cases hx0 : x = 0
      · exact ⟨u, hu, by simp [hx0, hu]⟩
      · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        refine ⟨‖x‖⁻¹ • x, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne'], ?_⟩
        have hinv : 1 ≤ ‖x‖⁻¹ := one_le_inv_iff₀.mpr ⟨hxpos, hxle⟩
        rw [show x - ‖x‖⁻¹ • x = (1 - ‖x‖⁻¹) • x by rw [sub_smul, one_smul], norm_smul,
          Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        field_simp
        ring
    have hzB : z ∈ B := mem_closedBall_zero_iff.mpr hz1.le
    have := hLip.dist_le_mul x hx z hzB
    rwa [dist_eq_norm, dist_eq_norm, hsph z hz1, sub_zero, hxz] at this
  have key : ∀ x y : E, ‖x‖ ≤ 1 → ¬ ‖y‖ ≤ 1 → ‖h x‖ ≤ C * ‖x - y‖ := fun x y hx hy =>
    (hbd x (mem_closedBall_zero_iff.mpr hx)).trans (mul_le_mul_of_nonneg_left
      (by linarith [norm_sub_norm_le y x, norm_sub_rev x y, not_le.mp hy]) C.coe_nonneg)
  -- by cases on which of `x`, `y` lie in the ball
  split_ifs with hx hy hy
  · have := hLip.dist_le_mul x (mem_closedBall_zero_iff.mpr hx) y (mem_closedBall_zero_iff.mpr hy)
    rwa [dist_eq_norm, dist_eq_norm] at this
  · simpa using key x y hx hy
  · rw [zero_sub, norm_neg, norm_sub_rev x y]; exact key y x hy hx
  · simp [mul_nonneg]


/-- For small `t ≥ 0`, `x + t (r x - x)` maps the ball onto itself injectively with positive
Jacobian `1 + t h'`, so `∫_B det (1 + t h') = vol B`. -/
private theorem aux_setIntegral_det_eq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] {r : E → E} {h' : E → E →L[ℝ] E} {C : NNReal}
    (hnorm : ∀ x ∈ closedBall (0 : E) 1, ‖r x‖ = 1)
    (hh' : ∀ x ∈ closedBall (0 : E) 1,
      HasFDerivWithinAt (fun x => r x - x) (h' x) (closedBall 0 1) x)
    (hC' : ∀ x ∈ closedBall (0 : E) 1, ‖h' x‖ ≤ C)
    (hLip : LipschitzOnWith C (fun x => r x - x) (closedBall 0 1))
    (htLip : ∀ x y : E, ‖(if ‖x‖ ≤ 1 then r x - x else 0) - (if ‖y‖ ≤ 1 then r y - y else 0)‖
      ≤ C * ‖x - y‖)
    {t : ℝ} (ht0 : 0 ≤ t) (htC : t * C < 1) (ht1 : t ≤ 1) : -- --- CONCL ---
    ∫ x in closedBall (0 : E) 1, (ContinuousLinearMap.id ℝ E + t • h' x).det ∂μ =
      μ.real (closedBall (0 : E) 1) := by -- --- PROOF ---
  set B := closedBall (0 : E) 1
  set h : E → E := fun x => r x - x
  set ht : E → E := fun x => if ‖x‖ ≤ 1 then h x else 0
  set f : E → E := fun x => x + t • h x
  have hf' : ∀ x ∈ B, HasFDerivWithinAt f (ContinuousLinearMap.id ℝ E + t • h' x) B x :=
    fun x hx => (hasFDerivAt_id x).hasFDerivWithinAt.add ((hh' x hx).const_smul t)
  -- `f` maps `B` onto `B`: into by convexity, onto by a contraction for the extension
  have hmaps : f '' B = B := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hrx := hnorm x hx
      rw [mem_closedBall_zero_iff] at hx ⊢
      have hfx : f x = (1 - t) • x + t • r x := by
        simp only [f, h, smul_sub, sub_smul, one_smul]; abel
      rw [hfx]
      calc ‖(1 - t) • x + t • r x‖ ≤ ‖(1 - t) • x‖ + ‖t • r x‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * ‖r x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
        _ ≤ (1 - t) * 1 + t * 1 := by
          rw [hrx]; nlinarith
        _ = 1 := by ring
    -- onto: `x = y - t ĥ(x)` by Banach, for the extension `ĥ` of `h` by zero
    · intro y hy
      set T : E → E := fun x => y - t • ht x
      have hK : (⟨t, ht0⟩ * C : NNReal) < 1 := by
        rw [← NNReal.coe_lt_coe]; exact htC
      have hT : ContractingWith (⟨t, ht0⟩ * C) T := by
        refine ⟨hK, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
        simp only [T, dist_eq_norm]
        rw [show y - t • ht a - (y - t • ht b) = t • (ht b - ht a) by rw [smul_sub]; abel,
          norm_smul, Real.norm_of_nonneg ht0, NNReal.coe_mul]
        change t * _ ≤ t * C * _
        rw [mul_assoc, norm_sub_rev a b]
        exact mul_le_mul_of_nonneg_left (htLip b a) ht0
      set x := ContractingWith.fixedPoint T hT
      have hx : T x = x := ContractingWith.fixedPoint_isFixedPt hT
      -- outside the ball the extension is zero, so the fixed point would be `y` itself
      by_cases hxB : ‖x‖ ≤ 1
      · refine ⟨x, mem_closedBall_zero_iff.mpr hxB, ?_⟩
        simp only [T, ht, if_pos hxB] at hx
        show x + t • h x = y
        calc x + t • h x = (y - t • h x) + t • h x := by rw [hx]
          _ = y := sub_add_cancel _ _
      · exfalso
        simp only [T, ht, if_neg hxB, smul_zero, sub_zero] at hx
        exact hxB (hx ▸ mem_closedBall_zero_iff.mp hy)
  -- `f` is injective on `B`: `t h` moves points by less than their distance
  have hinj : Set.InjOn f B := by
    intro x hx y hy hxy
    have hxy' : x - y = t • (h y - h x) := by
      rw [smul_sub, sub_eq_sub_iff_add_eq_add]
      exact hxy.trans (add_comm _ _)
    have hle : ‖x - y‖ ≤ t * C * ‖x - y‖ := by
      have hl := hLip.dist_le_mul y hy x hx
      rw [dist_eq_norm, dist_eq_norm, norm_sub_rev y x] at hl
      calc ‖x - y‖ = t * ‖h y - h x‖ := by rw [hxy', norm_smul, Real.norm_of_nonneg ht0]
        _ ≤ t * (C * ‖x - y‖) := mul_le_mul_of_nonneg_left hl ht0
        _ = _ := by ring
    by_contra hne
    have : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    nlinarith
  -- the change of variables, with the Jacobian's sign known
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul μ measurableSet_closedBall hf'
    hinj (fun _ => (1 : ℝ))
  rw [hmaps] at hcv
  simp only [smul_eq_mul, mul_one] at hcv
  rw [setIntegral_congr_fun measurableSet_closedBall
    (fun x hx => abs_of_pos (aux_det_pos (h' x) (hC' x hx) ht0 htC))] at hcv
  rw [← hcv, setIntegral_const, smul_eq_mul, mul_one]


/-- No `C¹` map on an open `U ⊇ closedBall 0 1` takes `U` into the unit sphere and fixes the
sphere pointwise. -/
private theorem aux_no_contDiff_retraction_closedBall {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) (hBU : closedBall (0 : E) 1 ⊆ U)
    {r : E → E} (hr : ContDiffOn ℝ 1 r U) (hnorm : ∀ x ∈ U, ‖r x‖ = 1)
    (hfix : ∀ x, ‖x‖ = 1 → r x = x) : -- --- CONCL ---
    False := by -- --- PROOF ---
  classical
  borelize E
  set μ : Measure E := Measure.addHaar
  set B := closedBall (0 : E) 1
  set r' := fderiv ℝ r
  have hder : ∀ x ∈ U, HasFDerivAt r (r' x) x := fun x hx =>
    (((hr.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  -- `r` is `C¹` and, as `‖r‖ = 1`, singular everywhere on `U`
  have hcont : ContinuousOn r' U := hr.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdet0 : ∀ x ∈ U, (r' x).det = 0 := fun x hx =>
    aux_det_eq_zero (hder x hx) (Filter.eventually_of_mem (hU.mem_nhds hx) hnorm)
  -- `h = r - id`, which vanishes on the sphere
  set h : E → E := fun x => r x - x
  set h' : E → E →L[ℝ] E := fun x => r' x - ContinuousLinearMap.id ℝ E
  have hh' : ∀ x ∈ B, HasFDerivWithinAt h (h' x) B x := fun x hx =>
    ((hder x (hBU hx)).sub (hasFDerivAt_id x)).hasFDerivWithinAt
  have hh'c : ContinuousOn h' B := (hcont.mono hBU).sub continuousOn_const
  -- `h'` is bounded on the ball, so `h` is Lipschitz there
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn hh'c
  set C : NNReal := ⟨max C₀ 0, le_max_right _ _⟩
  have hC : ∀ x ∈ B, ‖h' x‖₊ ≤ C := fun x hx => by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hC₀ x hx).trans (le_max_left _ _)
  have hC' : ∀ x ∈ B, ‖h' x‖ ≤ C := fun x hx => by
    rw [← coe_nnnorm, NNReal.coe_le_coe]; exact hC x hx
  have hLip : LipschitzOnWith C h B :=
    (convex_closedBall 0 1).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hh' hC
  have hsph : ∀ x : E, ‖x‖ = 1 → h x = 0 := fun x hx => by simp [h, hfix x hx]
  have hr0 : ‖r 0‖ = 1 := hnorm 0 (hBU (mem_closedBall_self zero_le_one))
  -- for small `t`, the integral of `det (1 + t h')` is the volume
  have htLip := aux_norm_extension_sub_le h hLip hsph hr0
  have hsmall : ∀ t : ℝ, 0 ≤ t → t * C < 1 → t ≤ 1 →
      ∫ x in B, (ContinuousLinearMap.id ℝ E + t • h' x).det ∂μ = μ.real B :=
    fun t ht0 htC ht1 => aux_setIntegral_det_eq μ (fun x hx => hnorm x (hBU hx)) hh' hC' hLip
      htLip ht0 htC ht1
  -- the Lagrange nodes
  set d := Module.finrank ℝ E
  set s := Finset.range (d + 1)
  set t₀ : ℝ := 1 / (2 * ((C : ℝ) + 1))
  have ht₀ : 0 < t₀ := by positivity
  have ht₀C : t₀ * C < 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith [C.coe_nonneg]
  have ht₀1 : t₀ ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [C.coe_nonneg]
  set v : ℕ → ℝ := fun j => t₀ * ((j : ℝ) + 1) / ((d : ℝ) + 1)
  -- distinct, and all small enough
  have hv : Set.InjOn v s := by
    intro i _ j _ hij
    simp only [v] at hij
    have : ((i : ℝ) + 1) = (j : ℝ) + 1 :=
      mul_left_cancel₀ ht₀.ne' ((div_left_inj' (by positivity)).mp hij)
    exact_mod_cast (add_right_cancel this)
  have hvsmall : ∀ j ∈ s, 0 ≤ v j ∧ v j * C < 1 ∧ v j ≤ 1 := by
    intro j hj
    have hj' : (j : ℝ) + 1 ≤ (d : ℝ) + 1 := by
      have := Finset.mem_range.mp hj; exact_mod_cast this
    have hvle : v j ≤ t₀ := by
      simp only [v]; rw [div_le_iff₀ (by positivity)]; nlinarith
    have hv0 : 0 ≤ v j := by positivity
    exact ⟨hv0, lt_of_le_of_lt (mul_le_mul_of_nonneg_right hvle C.coe_nonneg) ht₀C,
      hvle.trans ht₀1⟩
  -- the Lagrange weights at `t = 1`, which sum to one
  set c := fun j => (Lagrange.basis s v j).eval 1
  have hsum : ∑ j ∈ s, c j = 1 := by
    have := congrArg (eval 1) (Lagrange.sum_basis hv ⟨0, by simp [s]⟩)
    simpa [eval_finsetSum] using this
  -- at `t = 1` the integrand is `det Dr = 0`, but interpolation makes it the volume
  have hint : ∀ j, IntegrableOn
      (fun x => (ContinuousLinearMap.id ℝ E + v j • h' x).det) B μ := fun j =>
    ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1)
      (ContinuousLinearMap.continuous_det.comp_continuousOn
        (fun x hx => continuousWithinAt_const.add ((hh'c x hx).const_smul (v j))))
  have hzero : ∀ x ∈ B, (0 : ℝ) =
      ∑ j ∈ s, (ContinuousLinearMap.id ℝ E + v j • h' x).det * c j := by
    intro x hx
    rw [← aux_det_eval_one hv (h' x)]
    have : ContinuousLinearMap.id ℝ E + (1 : ℝ) • h' x = r' x := by
      simp [h']
    rw [this, hdet0 x (hBU hx)]
  -- integrate the interpolation identity
  have hvol : (0 : ℝ) = μ.real B := by
    calc (0 : ℝ) = ∫ x in B, (0 : ℝ) ∂μ := by simp
      _ = ∫ x in B, ∑ j ∈ s, (ContinuousLinearMap.id ℝ E + v j • h' x).det * c j ∂μ :=
          setIntegral_congr_fun measurableSet_closedBall hzero
      _ = ∑ j ∈ s, (∫ x in B, (ContinuousLinearMap.id ℝ E + v j • h' x).det ∂μ) * c j := by
          rw [integral_finsetSum _ fun j _ => (hint j).mul_const _]
          exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
      _ = ∑ j ∈ s, μ.real B * c j := Finset.sum_congr rfl fun j hj => by
          obtain ⟨a, b, e⟩ := hvsmall j hj
          rw [hsmall _ a b e]
      _ = μ.real B := by rw [← Finset.mul_sum, hsum, mul_one]
  -- and the ball has positive volume
  have hpos : 0 < μ.real B :=
    ENNReal.toReal_pos (measure_closedBall_pos μ 0 one_pos).ne'
      (isCompact_closedBall (0 : E) 1).measure_lt_top.ne
  linarith

end


section
open scoped Manifold ContDiff

/-- The `C¹` case: a `C¹` self-map of the closed unit ball has a fixed point. -/
private theorem aux_exists_fixedPoint_of_contDiff {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {g : E → E} (hg : ContDiff ℝ 1 g)
    (hgB : ∀ x, ‖x‖ ≤ 1 → ‖g x‖ ≤ 1) : -- --- CONCL ---
    ∃ x, ‖x‖ ≤ 1 ∧ g x = x := by -- --- PROOF ---
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
  exact aux_no_contDiff_retraction_closedBall hUo hBU hr hnorm hfix


/-- Brouwer: a continuous map taking the closed unit ball into itself has a fixed point there. -/
private theorem aux_exists_fixedPoint_closedBall {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {f : E → E} (hf : Continuous f)
    (hfB' : Set.MapsTo f (closedBall (0 : E) 1) (closedBall 0 1)) : -- --- CONCL ---
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

end


/-- A nonempty complete convex set is a continuous retract of an inner product space. -/
private theorem aux_exists_retraction_convex {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : Set E}
    (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) : -- --- CONCL ---
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
private theorem aux_exists_fixedPoint_inner {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) {f : E → E} (hf : ContinuousOn f K)
    (hfK : Set.MapsTo f K K) : -- --- CONCL ---
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
  obtain ⟨z, -, hz⟩ := aux_exists_fixedPoint_closedBall hFc fun z hz =>
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
    (hfK : Set.MapsTo f K K) : -- --- CONCL ---
    ∃ x ∈ K, f x = x := by -- --- PROOF ---
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
