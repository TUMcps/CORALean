module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSetExact
public import CORALean.ContSet.ContSet.Interfaces
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Segment

@[expose] public section

/-!
# The chord repair of [1, Prop. 2] fails when `⊖` takes the whole chord union

`NonlinearSys.minkowskiDiff_chord_subset_reachSetExact` erodes each chord slice by `C`, then
`R̂_err`, and unites over `t`. Eroding the union instead fails under the same hypotheses: for
`ẋ = (1/2, 0)`, `Δt = 1`, the connected `X₀ = [0, 1] × [0, 3] ∪ [2, 3] × [0, 3] ∪ [0, 3] × [2, 3]`,
`M = I`, `v = (1, 0)`, `C` the segment from `(-1/2, 0)` to `0`, `R̂_err = {0}`, `c = (-1/4, 0)`, the
chords sweep `[0, 4] × [0, 3]`, the runs leave `(3/2, 2) × [0, 2)` empty, and the eroded union
holds `(7/4, 1)`. Linearizing at `cen(X₀) + (Δt/2) f = (7/4, 3/2)`, as [1] does, gives these
chords for a field that is `(1/2, 0)` on the runs and `(1, 0)`, with zero Jacobian, at that point.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the eroded chord union is not inside the time-interval reachable set in general

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix Pointwise Set


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A run of the constant field `w` on `[0, t]` is `x s = x 0 + s w`. -/
private theorem NonlinearSys.aux_eq_add_smul_of_hasDerivWithinAt {x : ℝ → Vec ℝ 2} {w : Vec ℝ 2}
    {t : ℝ} (hd : ∀ s ∈ Icc 0 t, HasDerivWithinAt x w (Icc 0 t) s) : -- --- CONCL ---
    ∀ s ∈ Icc 0 t, x s = x 0 + s • w := by -- --- PROOF ---
  -- `x s - s w` has derivative zero, so it is constant
  have hz : ∀ s ∈ Icc 0 t, HasDerivWithinAt (fun s => x s - s • w) 0 (Icc 0 t) s := fun s hs => by
    have := (hd s hs).sub ((hasDerivWithinAt_id s (Icc 0 t)).smul_const w)
    rwa [one_smul, sub_self] at this
  have hc := constant_of_has_deriv_right_zero (fun s hs => (hz s hs).continuousWithinAt)
    (fun s hs => (hz s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
  intro s hs
  have := hc s hs
  simp only [zero_smul, sub_zero] at this
  rw [← this]; abel

/-- The `Π`-shaped initial set, coordinatewise: a left leg, a right leg and a bar on top. -/
private theorem NonlinearSys.aux_mem_piShape (y : Vec ℝ 2) :
    y ∈ Icc ![0, 0] ![1, 3] ∪ Icc ![2, 0] ![3, 3] ∪ Icc ![0, 2] ![3, 3] ↔
      (0 ≤ y 0 ∧ y 0 ≤ 1 ∧ 0 ≤ y 1 ∧ y 1 ≤ 3) ∨ (2 ≤ y 0 ∧ y 0 ≤ 3 ∧ 0 ≤ y 1 ∧ y 1 ≤ 3) ∨
        (0 ≤ y 0 ∧ y 0 ≤ 3 ∧ 2 ≤ y 1 ∧ y 1 ≤ 3) := by
  simp only [mem_union, mem_Icc, Pi.le_def, Fin.forall_fin_two]
  simp
  tauto


-- =======================================  MAIN THEOREM  ======================================= --

/-- `⊖` over the whole chord union, under the hypotheses of the per-slice repair of [1, Prop. 2],
is not inside the time-interval reachable set. -/
theorem NonlinearSys.minkowskiDiff_iUnion_chord_counterexample : -- --- CONCL ---
    ¬ ∀ (n m : ℕ) (sys : NonlinearSys n m) (R₀ : Set (Vec ℝ n)) (U : Set (Vec ℝ m)) (Δt : ℝ)
      (M : Mat ℝ n n),
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
  -- the instance: `ẋ = w = (1/2, 0)`, chords pushed by `v = (1, 0)`, `E = C` a segment
  set w : Vec ℝ 2 := ![1 / 2, 0]
  set sys : NonlinearSys 2 1 := ⟨fun _ _ => w, 0, fun _ _ => 0⟩
  set X₀ : Set (Vec ℝ 2) := Icc ![0, 0] ![1, 3] ∪ Icc ![2, 0] ![3, 3] ∪ Icc ![0, 2] ![3, 3]
  set C : Set (Vec ℝ 2) := segment ℝ ![-1 / 2, 0] 0
  have hC : C + ({0} : Set (Vec ℝ 2)) = C := add_zero C
  -- the chord of `x₀` is `x₀ + t (1, 0)`
  have hchord : ∀ (t : ℝ) (x₀ : Vec ℝ 2),
      x₀ + (t / 1) • ((1 : Mat ℝ 2 2) *ᵥ x₀ + ![1, 0] - x₀) = x₀ + t • ![1, 0] := fun t x₀ => by
    rw [one_mulVec, div_one, add_sub_cancel_left]
  have hCc : IsCompact C := by
    show IsCompact (segment ℝ _ _)
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have key := h 2 1 sys X₀ univ 1 1
    (fun t _ => by rw [div_one, ← add_smul, sub_add_cancel, one_smul, det_one]; exact isUnit_one)
    ![1, 0] C {0} (by rw [hC]; exact hCc) (by rw [hC]; exact convex_segment _ _)
    (by rw [hC]; exact ⟨0, right_mem_segment ℝ _ _⟩) ![-1 / 4, 0]
    (fun e he => by
      -- the segment is symmetric about its midpoint `c`
      rw [hC] at he ⊢
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := he
      refine ⟨b, a, hb, ha, by linarith, ?_⟩
      ext i; fin_cases i <;> simp; linarith)
    0 (mem_univ _) univ 0 (LipschitzWith.const' w).lipschitzOnWith
    (fun x₀ _ => ⟨fun s => x₀ + s • w, by simp, fun t _ => ⟨mem_univ _,
      (((hasDerivAt_id t).smul_const w).const_add x₀).hasDerivWithinAt.congr_deriv (by simp; rfl)⟩⟩)
    (fun t ht x₀ _ x hx0 hd => by
      -- the run is `x₀ + t w`, `t (w - (1, 0)) = (-t/2, 0)` lies on the segment
      rw [hchord, aux_eq_add_smul_of_hasDerivWithinAt hd t ⟨ht.1, le_rfl⟩, hx0, hC]
      refine ⟨t, 1 - t, ht.1, by linarith [ht.2], by ring, ?_⟩
      rw [smul_zero, add_zero, add_sub_add_left_eq_sub, ← smul_sub]
      show t • ![-1 / 2, 0] = t • (![1 / 2, 0] - ![1, 0])
      congr 1; ext i; fin_cases i <;> simp; norm_num)
  -- `(7/4, 1)` is in the eroded union: `(9/4 - s, 1)`, `s ∈ [0, 1/2]`, is on a swept leg
  have hin : (![7 / 4, 1] : Vec ℝ 2) ∈ (fun s => s + (2 : ℝ) • ![-1 / 4, 0]) '' minkowskiDiff
      (minkowskiDiff (⋃ t ∈ Icc (0 : ℝ) 1,
        (fun x₀ => x₀ + (t / 1) • ((1 : Mat ℝ 2 2) *ᵥ x₀ + ![1, 0] - x₀)) '' X₀) C) {0} := by
    refine ⟨![9 / 4, 1], fun z hz => ?_, by ext i; fin_cases i <;> simp; norm_num⟩
    rw [mem_singleton_iff.mp hz, add_zero]
    intro y hy
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    simp only [hchord, mem_iUnion, mem_image]
    by_cases hs : a ≤ 1 / 2
    · -- `9/4 - a/2 ≥ 2`: the right leg, at `t = 0`
      refine ⟨0, ⟨le_rfl, zero_le_one⟩, ![9 / 4 - a / 2, 1],
        (aux_mem_piShape _).mpr (Or.inr (Or.inl ?_)), ?_⟩
      · simp; constructor <;> linarith
      · ext i; fin_cases i <;> simp; ring
    · -- below `2`: the left leg's corner `(1, 1)`, pushed by `5/4 - a/2`
      refine ⟨5 / 4 - a / 2, ⟨by linarith, by linarith⟩, ![1, 1],
        (aux_mem_piShape _).mpr (Or.inl (by norm_num)), ?_⟩
      ext i; fin_cases i <;> simp; linarith
  -- but no run reaches it: it would start at `(7/4 - t/2, 1)`, between the legs
  obtain ⟨t, ht, x, u, traj, hxt⟩ := mem_iUnion₂.mp (key hin)
  have hflow := traj.flow t ⟨ht.1, le_rfl⟩
  simp only [sys, intervalIntegral.integral_const, sub_zero] at hflow
  have h0 := (aux_mem_piShape _).mp traj.init
  have e0 := congrFun hxt 0
  have e1 := congrFun hxt 1
  rw [hflow] at e0 e1
  simp [w] at e0 e1
  rcases h0 with h0 | h0 | h0 <;> nlinarith [ht.1, ht.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
