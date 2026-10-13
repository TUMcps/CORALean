import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.Basic

/-!
# `[1, Prop. 7]` fails as printed

In `ℝ¹`, with no `u`: `F = {x ≤ 2, -x ≤ 4} = [-4, 2]`, which is its own projection,
`x̄ = 1`, `Hₓ = (1, -1)` so `X = [0, 2]`, the ball `P_Ball = [-1, 1]`, `ε = 2`. The weights
`Λ₀ = I`, `Λ₁ = I/3`, `Λ₂ = 2I/3`, `X₁ = 1/3`, `βₓ = 1/3` meet every line of `[1, Prop. 7, Eq. 45]`
as printed — the `Λ₂` line with its `- H_Ball x̄` — yet `d_H(X, F_proj) = 4 > ε`: the point
`-4` is `4` from `[0, 2]`. With the sign corrected (`projection_inner_of_cert`) the same
weights fail that line.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.projection_inner_of_cert_counterexample :
    ∃ (H : Mat ℝ 2 1) (F : Mat ℝ 2 0) (g : Vec ℝ 2) (Hx : Mat ℝ 2 1) (xbar : Vec ℝ 1)
      (HB : Mat ℝ 2 1) (hB : Vec ℝ 2) (ε : ℝ) (Λ₀ Λ₁ Λ₂ : Mat ℝ 2 2) (Γ : Mat ℝ 0 1)
      (βu : Vec ℝ 0) (X₁ : Mat ℝ 1 1) (X₂ : Mat ℝ 1 0) (βx : Vec ℝ 1),
      (∀ x, x ∈ (HPolytope.ineqs HB hB).construct ↔ ‖x‖ ≤ 1) ∧
      (∀ i j, 0 ≤ Λ₀ i j) ∧ (∀ i j, 0 ≤ Λ₁ i j) ∧ (∀ i j, 0 ≤ Λ₂ i j) ∧
      Λ₀ * Hx = H + F * Γ ∧ Λ₀ *ᵥ 1 ≤ g - H *ᵥ xbar + F *ᵥ βu ∧
      Λ₁ * H = Hx * X₁ ∧ Λ₁ * F = Hx * X₂ ∧ Λ₂ * H = HB - HB * X₁ ∧ Λ₂ * F = -(HB * X₂) ∧
      Λ₁ *ᵥ g ≤ hB - Hx *ᵥ βx ∧ Λ₂ *ᵥ g ≤ ε • hB - HB *ᵥ xbar + HB *ᵥ βx ∧
      ¬ Metric.hausdorffDist (HPolytope.ahPolytope xbar 1 (HPolytope.ineqs Hx 1))
        {x | ∃ u, H *ᵥ x + F *ᵥ u ≤ g} ≤ ε := by -- --- PROOF ---
  let M : Mat ℝ 2 1 := !![1; -1]
  refine ⟨M, 0, ![2, 4], M, ![1], M, ![1, 1], 2, 1, (1 / 3 : ℝ) • 1, (2 / 3 : ℝ) • 1, 0, 0,
    !![1 / 3], 0, ![1 / 3], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `P_Ball = {x ≤ 1, -x ≤ 1}` is the unit ball of `ℝ¹`
  · intro x
    rw [HPolytope.mem_ineqs_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    constructor
    · intro h i
      fin_cases i
      have h0 := h 0; have h1 := h 1
      simp [M, dotProduct] at h0 h1
      simp [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    · intro h i
      have h0 := h 0
      simp only [Real.norm_eq_abs, abs_le] at h0
      fin_cases i <;> simp [M, mulVec, dotProduct] <;> linarith [h0.1, h0.2]
  -- the printed rows of `[1, Prop. 7, Eq. 45]`, checked entry by entry
  · intro i j; fin_cases i <;> fin_cases j <;> simp
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [M]
  · intro i
    fin_cases i <;> norm_num [M, mulVec, dotProduct, Matrix.one_apply, Matrix.vecHead,
      Matrix.vecTail]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [M, Matrix.mul_apply]
  · ext i j; exact j.elim0
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [M, Matrix.mul_apply]
  · ext i j; exact j.elim0
  · intro i; fin_cases i <;> norm_num [M, mulVec, dotProduct, Matrix.vecHead, Matrix.vecTail]
  · intro i; fin_cases i <;> norm_num [M, mulVec, dotProduct, Matrix.vecHead, Matrix.vecTail]
  -- `-4 ∈ F_proj` is `4` from every point of `X = [0, 2]`
  · intro hle
    have hX : ∀ y ∈ HPolytope.ahPolytope ![1] (1 : Mat ℝ 1 1) (HPolytope.ineqs M 1),
        0 ≤ y 0 := by
      rintro _ ⟨z, hz, rfl⟩
      have := HPolytope.mem_ineqs_iff.mp hz 1
      simp [M, mulVec, dotProduct] at this ⊢
      linarith
    have hmem : (![-4] : Vec ℝ 1)
        ∈ {x : Vec ℝ 1 | ∃ u, M *ᵥ x + (0 : Mat ℝ 2 0) *ᵥ u ≤ ![2, 4]} :=
      ⟨0, fun i => by fin_cases i <;> norm_num [M]⟩
    have hne : (HPolytope.ahPolytope ![1] (1 : Mat ℝ 1 1) (HPolytope.ineqs M 1)).Nonempty := by
      refine ⟨![1], 0, HPolytope.mem_ineqs_iff.mpr fun i => ?_, by simp⟩
      fin_cases i <;> simp
    -- both sets are bounded, so `-4`'s distance to `X` is at most the Hausdorff distance
    have hbX : Bornology.IsBounded
        (HPolytope.ahPolytope ![1] (1 : Mat ℝ 1 1) (HPolytope.ineqs M 1)) := by
      refine (Metric.isBounded_closedBall (x := (0 : Vec ℝ 1)) (r := 2)).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      have h0 := HPolytope.mem_ineqs_iff.mp hz 0
      have h1 := HPolytope.mem_ineqs_iff.mp hz 1
      simp [M, dotProduct] at h0 h1
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i; fin_cases i
      simp [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    have hbF : Bornology.IsBounded
        {x : Vec ℝ 1 | ∃ u, M *ᵥ x + (0 : Mat ℝ 2 0) *ᵥ u ≤ ![2, 4]} := by
      refine (Metric.isBounded_closedBall (x := (0 : Vec ℝ 1)) (r := 4)).subset ?_
      rintro x ⟨u, hu⟩
      have h0 := hu 0
      have h1 := hu 1
      simp [M, dotProduct] at h0 h1
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i; fin_cases i
      simp [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    -- `infDist (-4) X ≤ d_H`, and every point of `X` is at least `0`
    have hd := Metric.infDist_le_hausdorffDist_of_mem hmem
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨_, hmem⟩ hne hbF hbX)
    rw [Metric.hausdorffDist_comm] at hle
    have h4 : 4 ≤ Metric.infDist (![-4] : Vec ℝ 1)
        (HPolytope.ahPolytope ![1] (1 : Mat ℝ 1 1) (HPolytope.ineqs M 1)) := by
      refine (Metric.le_infDist hne).mpr fun y hy => ?_
      have hy0 := hX y hy
      rw [dist_comm, dist_eq_norm]
      refine le_trans ?_ (norm_le_pi_norm (y - ![-4]) 0)
      simp [Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith)]
      linarith
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
