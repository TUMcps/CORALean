module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryHasDerivWithinAt
public import CORALean.ContSet.ContSet.Interfaces
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# The chord repair of [1, Prop. 2] fails over the whole chord union for a convex initial set too

`NonlinearSys.minkowskiDiff_iUnion_chord_counterexample` needs a nonconvex `X₀`; a box does too.
For `ẋ = (x₃, 1, 0)`, `Δt = 1`, `X₀ = [-1/2, -1/4] × [-1, 0] × [-1, 1]`, `M = I + e₁e₃ᵀ = e^{A}`,
`v = (-1/2, 0, -1)`, `C` the segment from `0` to `δ = (1/2, 1, 1)`, `R̂_err = {0}`, `c = δ/2`, every
run is its chord plus `tδ`, and the eroded union holds `0`: `-λδ` is in `X₀` for `λ ≥ 1/2` and on
the chord of `(λ/2 - 1/2, -λ, 1 - λ)` at `t = 1` for `λ ≤ 1/2`. A run through `0` starts at
`(0, -t, 0)`, outside `X₀`. The covering time jumps from `0` to `1`, so no continuous choice
exists (`NonlinearSys.add_mem_reachSetExact_of_chord_section`). `M`, `v`, `E` are free here.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the eroded chord union of a convex initial set is not inside the time-interval reachable set
  in general

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix Pointwise Set


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A run of `ẋ = (x₃, 1, 0)` on `[0, t]` is `x s = (x₀₁ + s x₀₃, x₀₂ + s, x₀₃)`. -/
private theorem NonlinearSys.aux_eq_of_hasDerivWithinAt_shearDrift {x : ℝ → Vec ℝ 3} {t : ℝ}
    (hd : ∀ s ∈ Icc 0 t, HasDerivWithinAt x ![x s 2, 1, 0] (Icc 0 t) s) : -- --- CONCL ---
    ∀ s ∈ Icc 0 t, x s = ![x 0 0 + s * x 0 2, x 0 1 + s, x 0 2] := by -- --- PROOF ---
  -- a function with zero derivative on `[0, t]` is constant there
  have hconst : ∀ g : ℝ → ℝ, (∀ s ∈ Icc 0 t, HasDerivWithinAt g 0 (Icc 0 t) s) →
      ∀ s ∈ Icc 0 t, g s = g 0 := fun g hg =>
    constant_of_has_deriv_right_zero (fun s hs => (hg s hs).continuousWithinAt)
      (fun s hs => (hg s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
  have hc : ∀ i, ∀ s ∈ Icc 0 t,
      HasDerivWithinAt (fun s => x s i) ((![x s 2, 1, 0] : Vec ℝ 3) i) (Icc 0 t) s :=
    fun i s hs => hasDerivWithinAt_pi.mp (hd s hs) i
  -- `x₃` is constant, `x₂ - s` too, and `x₁ - s x₀₃` then as well
  have h2 : ∀ s ∈ Icc 0 t, x s 2 = x 0 2 :=
    hconst (fun s => x s 2) fun s hs => by simpa using hc 2 s hs
  have h1 : ∀ s ∈ Icc 0 t, x s 1 - s = x 0 1 - 0 :=
    hconst (fun s => x s 1 - s) fun s hs =>
      ((hc 1 s hs).sub (hasDerivWithinAt_id s (Icc 0 t))).congr_deriv (by simp)
  have h0 : ∀ s ∈ Icc 0 t, x s 0 - s * x 0 2 = x 0 0 - 0 * x 0 2 :=
    hconst (fun s => x s 0 - s * x 0 2) fun s hs =>
      ((hc 0 s hs).sub ((hasDerivWithinAt_id s (Icc 0 t)).mul_const
        (x 0 2))).congr_deriv (by simp [h2 s hs])
  intro s hs
  ext i; fin_cases i <;> simp <;> linarith [h0 s hs, h1 s hs, h2 s hs]


/-- The box `X₀ = [-1/2, -1/4] × [-1, 0] × [-1, 1]`, coordinatewise. -/
private theorem NonlinearSys.aux_mem_box_shearDrift (y : Vec ℝ 3) :
    y ∈ Icc ![-1 / 2, -1, -1] ![-1 / 4, 0, 1] ↔ (-1 / 2 ≤ y 0 ∧ y 0 ≤ -1 / 4) ∧
      (-1 ≤ y 1 ∧ y 1 ≤ 0) ∧ (-1 ≤ y 2 ∧ y 2 ≤ 1) := by
  simp only [mem_Icc, Pi.le_def, Fin.forall_fin_succ, IsEmpty.forall_iff]
  simp
  tauto

/-- The chord of `x₀` at `t` is `(x₀₁ + t x₀₃ - t/2, x₀₂, x₀₃ - t)`. -/
private theorem NonlinearSys.aux_chord_shearDrift (t : ℝ) (x₀ : Vec ℝ 3) :
    x₀ + (t / 1) • (!![1, 0, 1; 0, 1, 0; 0, 0, 1] *ᵥ x₀ + ![-1 / 2, 0, -1] - x₀) =
      ![x₀ 0 + t * x₀ 2 - t / 2, x₀ 1, x₀ 2 - t] := by
  ext i; fin_cases i <;> simp [dotProduct, Fin.sum_univ_three, vecHead, vecTail] <;> ring

/-- The eroded chord union holds `0`: `-aδ` lies in `X₀` for `a ≥ 1/2` and on the chord of
`(a/2 - 1/2, -a, 1 - a)` at `t = 1` for `a ≤ 1/2`. -/
private theorem NonlinearSys.aux_zero_mem_shearDrift : -- --- CONCL ---
    (0 : Vec ℝ 3) ∈ (fun s => s + (2 : ℝ) • ![1 / 4, 1 / 2, 1 / 2]) '' minkowskiDiff
      (minkowskiDiff (⋃ t ∈ Icc (0 : ℝ) 1, (fun x₀ => x₀ + (t / 1) •
        (!![1, 0, 1; 0, 1, 0; 0, 0, 1] *ᵥ x₀ + ![-1 / 2, 0, -1] - x₀)) ''
          Icc ![-1 / 2, -1, -1] ![-1 / 4, 0, 1]) (segment ℝ 0 ![1 / 2, 1, 1]))
        {0} := by -- --- PROOF ---
  have hX : ∀ p q r : ℝ, (-1 / 2 ≤ p ∧ p ≤ -1 / 4) → (-1 ≤ q ∧ q ≤ 0) → (-1 ≤ r ∧ r ≤ 1) →
      (![p, q, r] : Vec ℝ 3) ∈ Icc ![-1 / 2, -1, -1] ![-1 / 4, 0, 1] := fun p q r hp hq hr =>
    (aux_mem_box_shearDrift _).mpr ⟨hp, hq, hr⟩
  refine ⟨![-1 / 2, -1, -1], fun z hz => ?_, by ext i; fin_cases i <;> simp; norm_num⟩
  rw [mem_singleton_iff.mp hz, add_zero]
  intro y hy
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  -- the point is `-aδ`
  have hy : ![-1 / 2, -1, -1] + (a • 0 + b • ![1 / 2, 1, 1]) = (![-a / 2, -a, -a] : Vec ℝ 3) := by
    ext i; fin_cases i <;> simp <;> linarith
  rw [hy]
  simp only [mem_iUnion, mem_image]
  by_cases hs : 1 / 2 ≤ a
  · -- `-aδ ∈ X₀`, at `t = 0`
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, ![-a / 2, -a, -a],
      hX _ _ _ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩, ?_⟩
    rw [aux_chord_shearDrift]
    ext i; fin_cases i <;> simp
  · -- the chord of `(a/2 - 1/2, -a, 1 - a)` at `t = 1`
    refine ⟨1, ⟨zero_le_one, le_rfl⟩, ![a / 2 - 1 / 2, -a, 1 - a],
      hX _ _ _ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩, ?_⟩
    rw [aux_chord_shearDrift]
    ext i; fin_cases i <;> simp; ring

/-- No run of `ẋ = (x₃, 1, 0)` from the box reaches `0` within `[0, 1]`: it would start at
`(0, -t, 0)`. -/
private theorem NonlinearSys.aux_zero_not_mem_shearDrift : -- --- CONCL ---
    (0 : Vec ℝ 3) ∉ ⋃ t ∈ Icc (0 : ℝ) 1, NonlinearSys.reachSetExact (S := 𝒮)
      (⟨fun x _ => ![x 2, 1, 0], 0, fun _ _ => 0⟩ : NonlinearSys 3 1) (Icc 0 t)
      (Icc ![-1 / 2, -1, -1] ![-1 / 4, 0, 1]) univ t := by -- --- PROOF ---
  intro h0
  obtain ⟨t, ht, x, u, traj, hxt⟩ := mem_iUnion₂.mp h0
  have hf : ContinuousOn (fun s => (![x s 2, 1, 0] : Vec ℝ 3)) (Icc 0 t) := by
    refine continuousOn_pi.mpr fun i => ?_
    fin_cases i
    · exact (continuous_apply 2).comp_continuousOn traj.cont
    · exact continuousOn_const
    · exact continuousOn_const
  have hx := aux_eq_of_hasDerivWithinAt_shearDrift
    (fun s hs => traj.hasDerivWithinAt ⟨le_rfl, ht.1⟩ hf hs) t ⟨ht.1, le_rfl⟩
  have hb := (aux_mem_box_shearDrift _).mp traj.init
  have e0 := congrFun hxt 0
  have e2 := congrFun hxt 2
  rw [hx] at e0 e2
  simp at e0 e2
  rw [e2, mul_zero, add_zero] at e0
  linarith [hb.1.2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `⊖` over the whole chord union, under the hypotheses of the per-slice repair of [1, Prop. 2],
is not inside the time-interval reachable set, even for a convex, compact, nonempty `X₀`. -/
theorem NonlinearSys.minkowskiDiff_iUnion_chord_convex_counterexample : -- --- CONCL ---
    ¬ ∀ (n m : ℕ) (sys : NonlinearSys n m) (R₀ : Set (Vec ℝ n)), Convex ℝ R₀ → IsCompact R₀ →
      R₀.Nonempty → ∀ (U : Set (Vec ℝ m)) (Δt : ℝ) (M : Mat ℝ n n),
      (∀ t ∈ Icc 0 Δt, IsUnit ((1 - t / Δt) • (1 : Mat ℝ n n) + (t / Δt) • M).det) →
      ∀ (v : Vec ℝ n) (C Rerr : Set (Vec ℝ n)), IsCompact (C + Rerr) → Convex ℝ (C + Rerr) →
      (C + Rerr).Nonempty → ∀ c : Vec ℝ n, (∀ e ∈ C + Rerr, (2 : ℝ) • c - e ∈ C + Rerr) →
      ∀ u₀ ∈ U, ∀ (Ω : Set (Vec ℝ n)) (K : NNReal), LipschitzOnWith K (fun x => sys.f x u₀) Ω →
      (∀ x₀ ∈ R₀, ∃ x : ℝ → Vec ℝ n, x 0 = x₀ ∧ ∀ t ∈ Icc 0 Δt,
        x t ∈ Ω ∧ HasDerivWithinAt x (sys.f (x t) u₀) (Icc 0 Δt) t) →
      (∀ t ∈ Icc 0 Δt, ∀ x₀ ∈ R₀, ∀ x : ℝ → Vec ℝ n, x 0 = x₀ →
        (∀ s ∈ Icc 0 t, HasDerivWithinAt x (sys.f (x s) u₀) (Icc 0 t) s) →
        x t - (x₀ + (t / Δt) • (M *ᵥ x₀ + v - x₀)) ∈ C + Rerr) →
      (fun s => s + (2 : ℝ) • c) '' minkowskiDiff (minkowskiDiff
          (⋃ t ∈ Icc 0 Δt, (fun x₀ => x₀ + (t / Δt) • (M *ᵥ x₀ + v - x₀)) '' R₀) C) Rerr
        ⊆ ⋃ t ∈ Icc 0 Δt, sys.reachSetExact (S := 𝒮) (Icc 0 t) R₀ U t := by -- --- PROOF ---
  intro h
  -- `C = [0, δ]`, `δ = (1/2, 1, 1)`, `R̂_err = {0}`
  have hC : segment ℝ 0 (![1 / 2, 1, 1] : Vec ℝ 3) + {0} = segment ℝ 0 ![1 / 2, 1, 1] :=
    add_zero _
  have hCc : IsCompact (segment ℝ 0 (![1 / 2, 1, 1] : Vec ℝ 3)) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  -- the field `(x₃, 1, 0)` is `1`-Lipschitz in the sup norm
  have hLip : LipschitzWith 1 (fun x : Vec ℝ 3 => (![x 2, 1, 0] : Vec ℝ 3)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
    intro i
    fin_cases i
    · simpa using dist_le_pi_dist x y 2
    · simp
    · simp
  refine aux_zero_not_mem_shearDrift (h 3 1 ⟨fun x _ => ![x 2, 1, 0], 0, fun _ _ => 0⟩
    (Icc ![-1 / 2, -1, -1] ![-1 / 4, 0, 1]) (convex_Icc _ _) isCompact_Icc
    ⟨![-1 / 2, -1, -1], (aux_mem_box_shearDrift _).mpr (by simp; norm_num)⟩ univ 1
    !![1, 0, 1; 0, 1, 0; 0, 0, 1] (fun t _ => by rw [Matrix.det_fin_three]; simp)
    ![-1 / 2, 0, -1] (segment ℝ 0 ![1 / 2, 1, 1]) {0} (by rw [hC]; exact hCc)
    (by rw [hC]; exact convex_segment _ _) (by rw [hC]; exact ⟨0, left_mem_segment ℝ _ _⟩)
    ![1 / 4, 1 / 2, 1 / 2] (fun e he => ?_) 0 (mem_univ _) univ 1 hLip.lipschitzOnWith
    (fun x₀ _ => ⟨fun s => ![x₀ 0 + s * x₀ 2, x₀ 1 + s, x₀ 2], by ext i; fin_cases i <;> simp,
      fun t _ => ⟨mem_univ _, ?_⟩⟩) (fun t ht x₀ _ x hx0 hd => ?_) aux_zero_mem_shearDrift)
  · -- the segment is symmetric about its midpoint `c`
    rw [hC] at he ⊢
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := he
    refine ⟨b, a, hb, ha, by linarith, ?_⟩
    ext i; fin_cases i <;> simp <;> linarith
  · -- the run `(x₀₁ + t x₀₃, x₀₂ + t, x₀₃)`
    refine hasDerivWithinAt_pi.mpr fun i => ?_
    fin_cases i
    · simpa using ((hasDerivAt_id t).mul_const (x₀ 2)).const_add (x₀ 0) |>.hasDerivWithinAt
    · simpa using ((hasDerivAt_id t).const_add (x₀ 1)).hasDerivWithinAt
    · simpa using (hasDerivAt_const t (x₀ 2)).hasDerivWithinAt
  · -- every run is its chord plus `t δ`, a point of the segment
    have hx := aux_eq_of_hasDerivWithinAt_shearDrift hd t ⟨ht.1, le_rfl⟩
    rw [aux_chord_shearDrift, hx, hx0, hC]
    refine ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, ?_⟩
    ext i; fin_cases i <;> simp; ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
