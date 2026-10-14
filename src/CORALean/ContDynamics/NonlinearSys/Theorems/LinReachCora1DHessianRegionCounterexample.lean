module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachCora1D
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

/-!
# CORA's `'lin'` step accepts a set that misses a reachable state

For `ẋ = f(x) = 1 - (1001/750) x + (1001/3000) x⁴` from `x(0) = 0`, `Δt = 2`, CORA's step
(`linReachCora1D`) linearizes at `p = 1`, where `f(1) = -1/1000` and `f'(1) = 0`. The linearized
run drifts from `0` to `-1/500`, away from `p`, so the loop's region `Rmax + p` is about
`[-1/500, 2·10⁻⁵]`. `priv_abstrerr_lin` reads `f''(x) = (1001/250) x²` only there, below
`2·10⁻⁵`, takes `½ dx² max|f''| ≈ 8·10⁻⁶` (`dx ≈ 1`), its second pass accepts that, and `Rti`
ends below `1/50000`. But [1, Prop. 1] needs `f''` over the range of `ξ`, the segment from `p`,
which crosses `[0, 1]`, where `f''` reaches `4`: the remainder at `0` is `1001/1000`. The run
from `0` starts at speed `1` and is at `x(1/4) ≥ 1/20`. `hess` is the exact maximum of `|f''|`
over a box, what CORA's interval `x1^2` (`interval/power.m`) gives, so the miss is the region,
not overestimation; CORA's confinement check, `trueError ≤ appliedError`, passes.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with
      Uncertain Parameters using Conservative Linearization". In Proc. of the 47th IEEE
      Conference on Decision and Control (CDC), 2008, pp. 4042-4048.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Metric
open scoped NNReal


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- CORA's step on the example: two passes of the loop, then `Rti`'s upper end. -/
theorem aux_linReachCora1D_step :
    ∃ R, NonlinearSys.linReachCora1D (fun x : ℝ => 1 - 1001 / 750 * x + 1001 / 3000 * x ^ 4)
      (fun x => -(1001 / 750) + 1001 / 750 * x ^ 3)
      (fun lo hi => 1001 / 250 * max (lo ^ 2) (hi ^ 2)) ⟨0, 0⟩ 2 2 = some R ∧
      R.1.sup < 1 / 50000 := by
  simp only [NonlinearSys.linReachCora1D, abstrErrLoop]
  norm_num

/-- A run of `ẋ = f(x)` from `0` on `[0, 1/4]` that is at least `1/20` at its end. -/
theorem aux_linReachCora1D_run (f f' : ℝ → ℝ)
    (hfd : f = fun x : ℝ => 1 - 1001 / 750 * x + 1001 / 3000 * x ^ 4)
    (hf'd : f' = fun x : ℝ => -(1001 / 750) + 1001 / 750 * x ^ 3)
    (hf : ∀ x, HasDerivAt f (f' x) x) :
    ∃ x : ℝ → ℝ, x 0 = 0 ∧
        (∀ t ∈ Icc (0 : ℝ) (1 / 4), HasDerivWithinAt x (f (x t)) (Icc 0 (1 / 4)) t) ∧
        1 / 20 ≤ x (1 / 4) := by -- --- PROOF ---
  -- Picard-Lindelöf on `[0, 1/4]` in the ball `|x| ≤ 1/2`, where `|f| ≤ 2` and `|f'| ≤ 2`
  have hball : ∀ x ∈ closedBall (0 : ℝ) ((1 / 2 : ℝ≥0) : ℝ), -(1 / 2) ≤ x ∧ x ≤ 1 / 2 := by
    intro x hx
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx
    norm_num at hx
    exact abs_le.mp hx
  have hlip : LipschitzOnWith 2 f (closedBall (0 : ℝ) ((1 / 2 : ℝ≥0) : ℝ)) := by
    refine (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (hf x).hasDerivWithinAt) fun x hx => ?_
    obtain ⟨h1, h2⟩ := hball x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, hf'd]
    simp only [NNReal.coe_ofNat]
    have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg x]
  -- `|f| ≤ 2` on the ball and `2 · 1/4 ≤ 1/2`
  have hpl : IsPicardLindelof (fun _ : ℝ => f) (⟨0, by norm_num⟩ : Icc (0 : ℝ) (1 / 4)) (0 : ℝ)
      (1 / 2) 0 2 2 := by
    refine ⟨fun _ _ => hlip, fun _ _ => continuousOn_const, fun _ _ x hx => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hball x hx
      rw [Real.norm_eq_abs, hfd]
      simp only [NNReal.coe_ofNat]
      have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
      have hx4 : x ^ 4 ≤ 1 / 16 := by nlinarith [sq_nonneg x]
      rw [abs_le]
      constructor <;> nlinarith [pow_two_nonneg (x ^ 2)]
    · norm_num
  -- the solution of `next`'s fixed point, which stays in the ball
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl (mem_closedBall_self le_rfl)
  have hder : ∀ t ∈ Icc (0 : ℝ) (1 / 4),
      HasDerivWithinAt α.compProj (f (α.compProj t)) (Icc 0 (1 / 4)) t := by
    intro t ht
    apply ODE.hasDerivWithinAt_picard_Icc (⟨0, by norm_num⟩ : Icc (0 : ℝ) (1 / 4)).2
      hpl.continuousOn_uncurry α.continuous_compProj.continuousOn
      (fun _ _ => α.compProj_mem_closedBall hpl.mul_max_le) 0 ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  have h0 : α.compProj 0 = 0 := by
    have := ODE.FunSpace.compProj_val (α := α) (t := (⟨0, by norm_num⟩ : Icc (0 : ℝ) (1 / 4)))
    rw [this, ← hα, ODE.FunSpace.next_apply₀]
  refine ⟨α.compProj, h0, hder, ?_⟩
  -- in the ball `f ≥ 1/5`, so `x(t) - t/5` grows
  have hmono : MonotoneOn (fun t => α.compProj t - t / 5) (Icc (0 : ℝ) (1 / 4)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => f (α.compProj t) - 1 / 5)
      (convex_Icc _ _) ?_ ?_ ?_
    · exact fun t ht => ((hder t ht).continuousWithinAt).sub
        (continuousWithinAt_id.div_const 5)
    · intro t ht
      rw [interior_Icc] at ht ⊢
      have h := (hder t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self
      exact (h.sub ((hasDerivWithinAt_id t _).div_const 5)).congr_deriv (by simp)
    · intro t _
      obtain ⟨h1, h2⟩ := hball _ (α.compProj_mem_closedBall hpl.mul_max_le (t := t))
      simp only [hfd]
      nlinarith [pow_two_nonneg (α.compProj t ^ 2)]
  have := hmono ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num : (0 : ℝ) ≤ 1 / 4)
  simp only [h0] at this
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `'lin'` step for `ẋ = f(x)` from `{0}`, `Δt = 2`, with `f'`, `f''` the derivatives and
`hess` the exact maximum of `|f''|` over a box, settles on an `Rti` ending below `1/50000`; a run
from `0` is at `x(1/4) ≥ 1/20`. -/
theorem NonlinearSys.linReachCora1D_hessianRegion_counterexample :
    let f : ℝ → ℝ := fun x => 1 - 1001 / 750 * x + 1001 / 3000 * x ^ 4
    let f' : ℝ → ℝ := fun x => -(1001 / 750) + 1001 / 750 * x ^ 3
    let hess : ℝ → ℝ → ℝ := fun lo hi => 1001 / 250 * max (lo ^ 2) (hi ^ 2)
    (∀ x, HasDerivAt f (f' x) x) ∧ (∀ x, HasDerivAt f' (1001 / 250 * x ^ 2) x) ∧
      (∀ lo hi y, y ∈ Icc lo hi → |1001 / 250 * y ^ 2| ≤ hess lo hi) ∧
      (∃ R, NonlinearSys.linReachCora1D f f' hess ⟨0, 0⟩ 2 2 = some R ∧ R.1.sup < 1 / 50000) ∧
      ∃ x : ℝ → ℝ, x 0 = 0 ∧
        (∀ t ∈ Icc (0 : ℝ) (1 / 4), HasDerivWithinAt x (f (x t)) (Icc 0 (1 / 4)) t) ∧
        1 / 20 ≤ x (1 / 4) := by -- --- PROOF ---
  intro f f' hess
  -- the derivatives of the quartic
  have hf : ∀ x, HasDerivAt f (f' x) x := fun x =>
    ((((hasDerivAt_id' x).const_mul (1001 / 750 : ℝ)).const_sub 1).add
      ((hasDerivAt_pow 4 x).const_mul (1001 / 3000 : ℝ))).congr_deriv (by norm_num; ring)
  have hf' : ∀ x, HasDerivAt f' (1001 / 250 * x ^ 2) x := fun x =>
    (((hasDerivAt_pow 3 x).const_mul (1001 / 750 : ℝ)).const_add (-(1001 / 750))).congr_deriv
      (by norm_num; ring)
  refine ⟨hf, hf', ?_, aux_linReachCora1D_step, aux_linReachCora1D_run f f' rfl rfl hf⟩
  -- `y²` is at most the larger of the end points' squares
  intro lo hi y hy
  rw [abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rcases le_total 0 y with h0 | h0
  · exact le_max_of_le_right (by nlinarith [hy.2])
  · exact le_max_of_le_left (by nlinarith [hy.1])

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
