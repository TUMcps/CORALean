module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Lattice
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

/-!
# `linReachCora1D`, CORA's `'lin'` step in one dimension at a vanishing Jacobian

CORA's `@contDynamics/linReach.m` at `alg = 'lin'`, `tensorOrder = 2`, default `maxError = Inf`,
without inputs, line by line: `linearize` (`p = cx + f(cx)·Δt/2`), `oneStep` from `Rdelta`, the
`while perfIndCurr > 1` loop over `priv_abstrerr_lin` ([1, Prop. 1], its Hessian read over
`interval(Rmax) + p`), and `Rerror`. Sets are `Real.Interval ℝ`: in 1D a zonotope is its
interval hull, and `enclose(X, X + v)` is `conv(X ∪ (X + v))`. Only `A = f'(p) = 0` is modelled
(else `none`): there `eAdt = 1`, `E = F = G = 0`, `particularSolution_constant` is `Δt · uTrans`
(`Ainv` is empty) and `particularSolution_timeVarying` of a box `V` is `Δt · V`; `PU = 0`, `du = 0`.

`hess lo hi` is CORA's `max(infimum(abs(H)), supremum(abs(H)))` for its interval Hessian over
`totalInt_x = [lo, hi]`, supplied as the user's Hessian file supplies it. At `maxError = Inf`,
`perfInd` is zero, so the loop is `abstrErrLoop` with factor `1.1` and test `perfIndCurr ≤ 1`,
over the reals `trueError ≤ appliedError` (`0/0`, `NaN`, also ends MATLAB's loop); it states no
iteration count, so `fuel` is an argument and the result an `Option`.

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


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `'lin'` step for `ẋ = f(x)` from `Rinit`, Jacobian `f'`, Hessian bound `hess`:
`(Rti, Rtp)` as intervals, or `none` when `f'(p) ≠ 0` or `fuel` passes have not
settled. -/
noncomputable def NonlinearSys.linReachCora1D (f f' : ℝ → ℝ) (hess : ℝ → ℝ → ℝ)
    (Rinit : Real.Interval ℝ) (Δt : ℝ) (fuel : ℕ) :
    Option (Real.Interval ℝ × Real.Interval ℝ) :=
  -- linearize
  let cx := (Rinit.inf + Rinit.sup) / 2                       -- cx = center(R)
  let f0prev := f cx                                      -- f0prev = nlnsys.mFile(cx,p.u)
  let p := cx + f0prev * (1 / 2) * Δt                     -- p.x = cx + f0prev*0.5*timeStep
  let f0 := f p                                           -- f0 = nlnsys.mFile(p.x,p.u)
  let A := f' p                                           -- [A,B] = nlnsys.jacobian(p.x,p.u)
  if A ≠ 0 then none else
  let Rdelta : Real.Interval ℝ := ⟨Rinit.inf - p, Rinit.sup - p⟩          -- Rdelta = Rinit + (-p.x)
  -- oneStep at `A = 0`
  let Pu := Δt * f0                                       -- particularSolution_constant
  let Htp : Real.Interval ℝ := ⟨Rdelta.inf + Pu, Rdelta.sup + Pu⟩           -- Htp = eAdt*X + Pu
  -- Hti = enclose(X,Htp) + C_state
  let Hti : Real.Interval ℝ := ⟨min Rdelta.inf Htp.inf, max Rdelta.sup Htp.sup⟩
  let Rtp := Htp                                          -- Rtp = Htp + PU
  let Rti := Hti                                          -- Rti = Hti + PU + C_input
  -- the true error induced by an applied one
  let Φ : ℝ → ℝ := fun appliedError =>
    let RallError := Δt * appliedError                    -- particularSolution_timeVarying
    -- Rmax = Rti + RallError
    let Rmax : Real.Interval ℝ := ⟨Rti.inf - RallError, Rti.sup + RallError⟩
    let totalInt : Real.Interval ℝ := ⟨Rmax.inf + p, Rmax.sup + p⟩         -- totalInt_x = IHx + p.x
    let H := hess totalInt.inf totalInt.sup                   -- H_ = max(inf(abs(H)),sup(abs(H)))
    let dx := max |Rmax.inf| |Rmax.sup|                     -- dx = max(abs(inf(IHx)),abs(sup(IHx)))
    1 / 2 * dx * H * dx                                   -- errorLagr = 0.5*dz'*H_*dz
  -- while perfIndCurr > 1: appliedError = 1.1*abstrerr, from abstrerr = 0
  match abstrErrLoop (S := fun _ => ℝ) (n := 1) (fun te ae => decide (te ≤ ae))
      (fun e => 11 / 10 * e) Φ 0 fuel with
  | none => none
  | some trueError =>
    let Rerror := Δt * trueError                          -- particularSolution_timeVarying
    some (⟨Rti.inf + p - Rerror, Rti.sup + p + Rerror⟩,       -- Rti = Rti + p.x + Rerror
      ⟨Rtp.inf + p - Rerror, Rtp.sup + p + Rerror⟩)           -- Rtp = Rtp + p.x + Rerror


open Set Metric
open scoped NNReal


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- CORA's step on the example: two passes of the loop, then `Rti`'s upper end. -/
theorem aux_linReachCora1D_step : -- --- STMT ---
    ∃ R, NonlinearSys.linReachCora1D (fun x : ℝ => 1 - 1001 / 750 * x + 1001 / 3000 * x ^ 4)
      (fun x => -(1001 / 750) + 1001 / 750 * x ^ 3)
      (fun lo hi => 1001 / 250 * max (lo ^ 2) (hi ^ 2)) ⟨0, 0⟩ 2 2 = some R ∧
      R.1.sup < 1 / 50000 := by -- --- PROOF ---
  simp only [NonlinearSys.linReachCora1D, abstrErrLoop]
  norm_num

/-- A run of `ẋ = f(x)` from `0` on `[0, 1/4]` that is at least `1/20` at its end. -/
theorem aux_linReachCora1D_run (f f' : ℝ → ℝ)
    (hfd : f = fun x : ℝ => 1 - 1001 / 750 * x + 1001 / 3000 * x ^ 4)
    (hf'd : f' = fun x : ℝ => -(1001 / 750) + 1001 / 750 * x ^ 3)
    (hf : ∀ x, HasDerivAt f (f' x) x) : -- --- STMT ---
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
theorem NonlinearSys.linReachCora1D_hessianRegion_counterexample : -- --- STMT ---
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
