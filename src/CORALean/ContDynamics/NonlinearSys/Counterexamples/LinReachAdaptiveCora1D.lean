module

public import Mathlib.Data.Real.Basic
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

/-!
# `abstrErrAdaptiveCora1D`, CORA's `priv_abstractionError_adaptive` in one dimension

CORA's `@nonlinearSys/private/priv_abstractionError_adaptive.m` at `alg = 'lin'`,
`tensorOrder = 2`, without inputs (`U = 0`, so `du = 0`), line by line: the box of `R = Rmax`,
shifted by the linearization point `p` to `totalInt_x`, its largest magnitude `dx`, and the
Lagrange term `0.5 * dz' * H_ * dz` of [1, Prop. 1] with the Hessian read over `totalInt_x`.

Intervals are `Real.Interval ℝ`, read through `inf` and `sup`. `hessIv lo hi` is CORA's interval
Hessian `H` over `[lo, hi]`, as the user's Hessian file evaluates it;
`max(infimum(abs(H)), supremum(abs(H)))` is `max |inf H| |sup H|`. `hessianConst` is
`options.hessianConst` once `options.isHessianConst` holds (`some`), else `none`;
the check that sets it runs in the caller.

# `adaptErrLoopCora1D`, the abstraction-error loop of CORA's `linReach_adaptive`

The inner `while true` loop of CORA's `@nonlinearSys/linReach_adaptive.m` at `alg = 'lin'`, in
one dimension: from an admissible error `error_adm`, compute the `trueError` it induces
(`Φ`, which the caller builds from `RallError`, `Rmax` and `priv_abstractionError_adaptive`),
accept it once it fits, else enlarge `error_adm` to `1.1 * trueError` and repeat; from the third
pass on, a `perfIndCurr` above the previous one gives up (`options.Lconverged = false`, `none`).

Over the reals with `trueError ≥ 0` and `error_adm ≥ 0`, `perfIndCurr <= 1 || ~any(trueError)`
is `trueError ≤ error_adm` (`trueError / 0` is `Inf` for a positive `trueError`, and a zero one
is `~any`). `perfIndCounter` starts at `1`; `perfInds(1)` is never compared. The loop states no
iteration count, so `fuel` bounds it and running out is `none`.

# `optimalDeltatCora`, CORA's `aux_optimaldeltat`

The time step size CORA's `@nonlinearSys/linReach_adaptive.m` tunes (`aux_optimaldeltat`, at
`alg = 'lin'`), line by line: the candidates `deltat * mu^k'` for `k' = 0, …, kprimemax`, the
estimate `objfuncset` of the set size after the finite horizon (eq. (57) of [2]), and its first
minimizer, `min`'s index. `rR` and `rerr1` are the radii the caller reads from `Rt` and `Rerr`;
`mu` is `opt.decrFactor`, `redFactor` is `opt.redFactor`.

This is the code, not [2]'s §5.4 (`optDeltat`, a descent that stops at the first increase): MATLAB's
`min` scans every candidate. The first minimizer is a left fold that moves only on a strict
decrease.

# `linReachAdaptiveCora1D`, the first step of CORA's `linReach_adaptive` in one dimension

CORA's `@nonlinearSys/linReach_adaptive.m` (`alg = 'lin-adaptive'`, `postProcessing`'s
`decrFactor = 0.9`, `redFactor = 0.0005`, `zetaphi(3) = 0.68`), first step (`options.i == 1`),
from a point `x0`, without inputs, line by line along the path whose tuned step is the finite
horizon `0.01 (tFinal - tStart)`: run 1 at the horizon (`veryfirststep`), run 1 at `decrFactor`
times it, the gain `varphi` against `zetaphi`, `aux_optimaldeltat` (`optimalDeltatCora`), and, the
tuned step being the horizon (`timeStepequalHorizon`), run 2 at `decrFactor` times it; the result
is the horizon run's sets. Each run is `linearize` (`p = x0 + f(x0)·Δt/2`), `initReach_adaptive`
and the error loop `adaptErrLoopCora1D` over `abstrErrAdaptiveCora1D`. Sets are
`Real.Interval ℝ`.

Only `A = f'(p) = 0` is modelled (else `none`): `aux_expmtie_adaptive` stops at `eta = 2` with
`E = F = 0`, so `Rhom_tp = Rdelta + Δt f(p)`, `Rhom = enclose(Rdelta, Rhom_tp)`, and
`errorSolution_adaptive` scales a box by `Δt`. A point start gives `tensorOrder = 2` and, by
`aux_getPowers` at `A = 0`, `minorder = 2`; a zero `trueError` makes `orders = Inf`, an indexing
error. Branches off the path (halving, a small `varphi`, a shorter tuned step) and running out of
`fuel` are `none`. The result is `(Rti, Rtp, options.Δt)`.

# CORA's adaptive `'lin'` step accepts a set that misses a reachable state

`linReach_adaptive` reads the Hessian over `interval(Rmax) + p` as `linReach` does, and its tuning
[2] does not save it. For `ẋ = f(x) = 1 - (59049/39400) x + (468559/236400) x⁶ - (40951/27580) x⁷`
from `x(0) = 0`, `tFinal = 200`, the first step (`linReachAdaptiveCora1D`) runs at the horizon
`Δt = 2` (`p = 1`) and at `9/5` (`p = 9/10`); `f' = 0` at both, `f(1) ≈ -0.0015`,
`f(9/10) ≈ -0.0057`, so each linearized run drifts away from `p` and each loop reads
`f''(x) ≈ 59.5 x⁴` near `0` only. The errors are `≈ 2.1·10⁻⁹` and `≈ 2.7·10⁻⁷`, the gain
`varphi ≈ 113` passes `0.68`, and `aux_optimaldeltat`, from a point, keeps the horizon (each
shorter candidate multiplies the estimate by at least `varphi / 2`). `Rti` ends below `1/50000`,
while the run is at `x(1/4) ≥ 1/20`: the remainder [1, Prop. 1] needs `f''` along `[0, 1]`.

`hessIv` is any interval Hessian of magnitude `f''(lo)` on boxes `[lo, hi]`, `lo ≤ 0`,
`hi ≤ -lo`, the only boxes the step reads: every interval Hessian between the range of `f''` and
the majorant `M` of its monomials has it, so CORA's interval `f''` in expanded, Horner or factored
form does. The miss is the region, not overestimation.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with
      Uncertain Parameters using Conservative Linearization". In Proc. of the 47th IEEE
      Conference on Decision and Control (CDC), 2008, pp. 4042-4048.
* [2] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `priv_abstractionError_adaptive` (`'lin'`, `tensorOrder = 2`) in 1D without inputs:
`trueError` for the box `Rmax`, linearization point `p`, interval Hessian `hessIv`. -/
noncomputable def NonlinearSys.abstrErrAdaptiveCora1D (hessIv : ℝ → ℝ → Real.Interval ℝ)
    (hessianConst : Option ℝ) (p : ℝ) (Rmax : Real.Interval ℝ) : ℝ :=
  let IH_x := Rmax                                        -- IH_x = interval(R)
  let totalInt_x : Real.Interval ℝ := ⟨IH_x.inf + p, IH_x.sup + p⟩        -- totalInt_x = IH_x + p.x
  let IHinf := |IH_x.inf|                                   -- IHinf = abs(infimum(IH_x))
  let IHsup := |IH_x.sup|                                   -- IHsup = abs(supremum(IH_x))
  let dx := max IHinf IHsup                               -- dx = max(IHinf,IHsup)
  match hessianConst with
  | none =>                                               -- if ~options.isHessianConst
    let H := hessIv totalInt_x.inf totalInt_x.sup             -- H = nlnsys.hessian(totalInt_x,...)
    let H_ := max |H.inf| |H.sup|                             -- H_ = max(infimum(H_),supremum(H_))
    1 / 2 * dx * H_ * dx                                  -- err(i,1) = 0.5 * dz' * H_ * dz
  | some H_ =>                                            -- use saved H_
    1 / 2 * dx * H_ * dx                                  -- err(i,1) = 0.5*dz'*hessianConst*dz


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's abstraction-error loop of `linReach_adaptive` in 1D: the accepted `trueError`, or
`none` when it gives up or `fuel` passes have not settled. -/
noncomputable def NonlinearSys.adaptErrLoopCora1D (Φ : ℝ → ℝ) :
    ℕ → ℕ → ℝ → ℝ → Option ℝ
  | 0, _, _, _ => none
  | fuel + 1, perfIndCounter, error_adm, perfIndPrev =>
    let trueError := Φ error_adm                          -- [..,trueError,..] = priv_abstr...(Rmax)
    let perfIndCurr := trueError / error_adm              -- perfIndCurr = max(trueError./error_adm)
    if trueError ≤ error_adm then some trueError          -- if perfIndCurr <= 1 || ~any(trueError)
    else if 2 < perfIndCounter ∧ perfIndPrev < perfIndCurr then none -- Lconverged = false
    else NonlinearSys.adaptErrLoopCora1D Φ fuel (perfIndCounter + 1) -- perfIndCounter + 1
      (11 / 10 * trueError) perfIndCurr                   -- error_adm = 1.1 * trueError


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `aux_optimaldeltat` at `alg = 'lin'`: the candidate time step size whose estimated
set size after the finite horizon `deltat` is smallest, the first one on ties. -/
noncomputable def NonlinearSys.optimalDeltatCora
    (rR rerr1 deltat varphimin zetaP mu redFactor : ℝ) : ℝ :=
  let dHused : ℝ := 1 / 2                                 -- dHused = 0.5 ('lin')
  let zetaZ := redFactor * dHused                         -- zetaZ = opt.redFactor * dHused
  let kprimemax := ⌈-Real.log 100 / Real.log mu⌉₊         -- kprimemax = ceil(-log(100)/log(mu))
  let kprime := List.range (kprimemax + 1)                -- kprime = 0:round(kprimemax)
  let k := fun j : ℕ => mu ^ (-(j : ℤ))                   -- k = mu .^ (-kprime)
  let deltats := fun j : ℕ => deltat * mu ^ j             -- deltats = deltat * mu.^kprime
  let floork := fun j : ℕ => ⌊k j⌋₊                       -- floork = floor(k)
  let varphimax := mu                                     -- varphimax = mu
  let varphi_h := varphimax - varphimin                   -- varphi_h = (varphimax - varphimin)
  let varphi := fun j : ℕ =>                              -- varphi = (varphimin + (deltats(1)
    (varphimin + (deltats 0 - deltats j) / deltats 0      --   - deltats)/deltats(1)
      * varphi_h) / mu                                    --   * varphi_h) / mu
  let varphiprod := fun j : ℕ =>                          -- varphiprod = cumprod(varphi)
    ∏ i ∈ Finset.range (j + 1), varphi i
  let sumallbutlast := fun j : ℕ =>                       -- sumallbutlast(i) = sum(
    ∑ i ∈ Finset.Icc 1 (floork j),                        --   (1:floork(i)) terms of
      (1 + 2 * zetaZ) ^ (k j + 1 - (i : ℝ))               --   firstfactor .*
        * zetaP ^ (1 - (i : ℝ) / k j)                     --   secondfactor)
  let objfuncset := fun j : ℕ =>                          -- objfuncset =
    rR * (1 + 2 * zetaZ) ^ (k j) * zetaP                  --   rR*(1+2*zetaZ).^k*zetaP
      + rerr1 / k j * varphiprod j                        --   + rerr1./k.*varphiprod.*
        * (sumallbutlast j                                --   (sumallbutlast + (1+zetaZ)
          + (1 + zetaZ) ^ (k j - (j : ℝ))                 --   .^(k-kprime)
            * (k j - (floork j : ℝ)))                     --   .*(k-floork))
  let bestIdxnew := kprime.foldl                          -- [~,bestIdxnew] = min(objfuncset)
    (fun b j => if objfuncset j < objfuncset b then j else b) 0
  deltats bestIdxnew                                      -- deltatest = deltats(bestIdxnew)


-- The model: CORA's code as printed, kept only to be refuted.
/-- The first step of CORA's `linReach_adaptive` (`'lin'`) for `ẋ = f(x)` from the point `x0`,
Jacobian `f'`, interval Hessian `hessIv`: `(Rti, Rtp, timeStep)`, or `none` off the path on which
the tuned time step is the finite horizon. -/
noncomputable def NonlinearSys.linReachAdaptiveCora1D (f f' : ℝ → ℝ)
    (hessIv : ℝ → ℝ → Real.Interval ℝ) (x0 tStart tFinal : ℝ) (fuel : ℕ) :
    Option (Real.Interval ℝ × (Real.Interval ℝ × ℝ)) :=
  let decrFactor : ℝ := 9 / 10                            -- options.decrFactor = 0.90
  let redFactor : ℝ := 5 / 10000                          -- options.redFactor = 0.0005
  let zetaphi : ℝ := 68 / 100                             -- options.zetaphi(options.minorder+1)
  let timeStep_h := (tFinal - tStart) * (1 / 100)         -- options.Δt = (tF - tS) * 0.01
  let finitehorizon := timeStep_h                         -- finitehorizon = options.Δt
  -- run 1 at the finite horizon (veryfirststep)
  let p_h := x0 + f x0 * (1 / 2) * timeStep_h             -- p.x = cx + f0prev*0.5*timeStep
  let f0_h := f p_h                                       -- f0 = nlnsys.mFile(p.x,p.u)
  let A_h := f' p_h                                       -- [A,B] = nlnsys.jacobian(p.x,p.u)
  if A_h ≠ 0 then none else
  let zetaP_h := Real.exp (A_h * timeStep_h)              -- zetaP = exp(trace(linsys.A*timeStep))
  let Rdelta_h := x0 - p_h                                -- Rdelta = Rstart + (-p.x)
  let Rlintp_h := Rdelta_h + timeStep_h * f0_h            -- Rhom_tp = eAt*Rstart + Rtrans
  -- Rhom = enclose(Rstart,Rhom_tp)
  let Rlinti_h : Real.Interval ℝ := ⟨min Rdelta_h Rlintp_h, max Rdelta_h Rlintp_h⟩
  -- aux_checkIfHessianConst, first call (error_adm = 0, Rmax = Rlinti): totalInt_x = IH_x + p.x
  let totalInt₀ : Real.Interval ℝ := ⟨Rlinti_h.inf + p_h, Rlinti_h.sup + p_h⟩
  let H₀ := hessIv totalInt₀.inf totalInt₀.sup                -- H = nlnsys.hessian(totalInt_x,..)
  let c₀ := (totalInt₀.inf + totalInt₀.sup) / 2               -- c = center(I)
  let r₀ := (totalInt₀.sup - totalInt₀.inf) / 2               -- r = rad(I)
  let H_test := hessIv (c₀ - r₀ * (11 / 10)) (c₀ + r₀ * (11 / 10)) -- obj.hessian(enlarge(..,1.1))
  let hessianConst : Option ℝ :=                          -- options.isHessianConst
    if H₀.inf = H_test.inf ∧ H₀.sup = H_test.sup then       --   = all(H{i} == H_test{i})
      some (max |H₀.inf| |H₀.sup|) else none
  let Φ_h := fun error_adm => NonlinearSys.abstrErrAdaptiveCora1D hessIv hessianConst p_h
    ⟨Rlinti_h.inf - timeStep_h * error_adm, Rlinti_h.sup + timeStep_h * error_adm⟩ -- Rmax
  match NonlinearSys.adaptErrLoopCora1D Φ_h fuel 1 0 0 with -- error_adm = error_adm_horizon = 0
  | none => none                                          -- ~Lconverged: halve timeStep
  | some trueError_h =>
  if trueError_h = 0 then none else                       -- aux_getPowers: orders = Inf
  let Rerror_h := timeStep_h * trueError_h                -- Rerror = errorSolution_adaptive(..)
  let abstrerr_h := Rerror_h                              -- abstrerr = sum(abs(generators(Rerror)))
  -- run 1 at decrFactor times the finite horizon
  let timeStep₁ := decrFactor * timeStep_h                -- options.Δt = decrFactor*timeStep
  let error_adm₁ := decrFactor * trueError_h              -- error_adm = decrFactor * trueError
  let p₁ := x0 + f x0 * (1 / 2) * timeStep₁               -- p.x = cx + f0prev*0.5*timeStep
  let f0₁ := f p₁                                         -- f0 = nlnsys.mFile(p.x,p.u)
  let A₁ := f' p₁                                         -- [A,B] = nlnsys.jacobian(p.x,p.u)
  if A₁ ≠ 0 then none else
  let Rdelta₁ := x0 - p₁                                  -- Rdelta = Rstart + (-p.x)
  let Rlintp₁ := Rdelta₁ + timeStep₁ * f0₁                -- Rhom_tp = eAt*Rstart + Rtrans
  -- Rhom = enclose(Rstart,Rhom_tp)
  let Rlinti₁ : Real.Interval ℝ := ⟨min Rdelta₁ Rlintp₁, max Rdelta₁ Rlintp₁⟩
  let Φ₁ := fun error_adm => NonlinearSys.abstrErrAdaptiveCora1D hessIv hessianConst p₁
    ⟨Rlinti₁.inf - timeStep₁ * error_adm, Rlinti₁.sup + timeStep₁ * error_adm⟩ -- Rmax
  match NonlinearSys.adaptErrLoopCora1D Φ₁ fuel 1 error_adm₁ 0 with
  | none => none                                          -- ~Lconverged: halve timeStep
  | some trueError₁ =>
  let abstrerr₁ := timeStep₁ * trueError₁                 -- abstrerr = sum(abs(generators(Rerror)))
  let varphi := abstrerr₁ / abstrerr_h                    -- varphi = max(errRatio(~isnan(..)))
  if varphi < zetaphi then none else                      -- decrease time step size
  let timeStep₂ := NonlinearSys.optimalDeltatCora 0 Rerror_h -- aux_optimaldeltat(Rstart,Rerror_h,
    finitehorizon varphi zetaP_h decrFactor redFactor     --   finitehorizon,varphi,zetaP_h,options)
  if timeStep₂ ≠ finitehorizon then none else             -- if options.Δt == finitehorizon
  -- run 2 (timeStepequalHorizon)
  let timeStep₃ := timeStep₂ * decrFactor                 -- options.Δt*options.decrFactor
  let p₃ := x0 + f x0 * (1 / 2) * timeStep₃               -- p.x = cx + f0prev*0.5*timeStep
  let f0₃ := f p₃                                         -- f0 = nlnsys.mFile(p.x,p.u)
  let A₃ := f' p₃                                         -- [A,B] = nlnsys.jacobian(p.x,p.u)
  if A₃ ≠ 0 then none else
  let Rdelta₃ := x0 - p₃                                  -- Rdelta = Rstart + (-p.x)
  let Rlintp₃ := Rdelta₃ + timeStep₃ * f0₃                -- Rhom_tp = eAt*Rstart + Rtrans
  -- Rhom = enclose(Rstart,Rhom_tp)
  let Rlinti₃ : Real.Interval ℝ := ⟨min Rdelta₃ Rlintp₃, max Rdelta₃ Rlintp₃⟩
  let Φ₃ := fun error_adm => NonlinearSys.abstrErrAdaptiveCora1D hessIv hessianConst p₃
    ⟨Rlinti₃.inf - timeStep₃ * error_adm, Rlinti₃.sup + timeStep₃ * error_adm⟩ -- Rmax
  match NonlinearSys.adaptErrLoopCora1D Φ₃ fuel 1 0 0 with -- error_adm = zeros
  | none => none                                          -- ~Lconverged: halve timeStep
  | some _ =>
  -- timeStepequalHorizon: Rti = Rti_h + linx_h, Rtp = Rtp_h + linx_h, Rerror = Rerror_h
  some (⟨Rlinti_h.inf + p_h - Rerror_h, Rlinti_h.sup + p_h + Rerror_h⟩, -- Rti = Rti + Rerror
    ⟨Rlintp_h + p_h - Rerror_h, Rlintp_h + p_h + Rerror_h⟩,        -- Rtp = Rtp + Rerror
    finitehorizon)                                        -- options.Δt = finitehorizon


open Set Metric
open scoped NNReal


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Two passes of the error loop: the first does not fit, the second does. -/
theorem aux_linReachAdaptiveCora1D_loop (Φ : ℝ → ℝ) (ae₀ prev : ℝ) (fuel : ℕ)
    (h1 : ae₀ < Φ ae₀)
    (h2 : Φ (11 / 10 * Φ ae₀) ≤ 11 / 10 * Φ ae₀) :
    NonlinearSys.adaptErrLoopCora1D Φ (fuel + 2) 1 ae₀ prev = some (Φ (11 / 10 * Φ ae₀)) := by
  simp [NonlinearSys.adaptErrLoopCora1D, not_le.mpr h1, h2]

/-- MATLAB's first minimizer stays at `0` when no candidate beats it. -/
theorem aux_linReachAdaptiveCora1D_firstMin (g : ℕ → ℝ) (h : ∀ j, g 0 ≤ g j) (l : List ℕ) :
    l.foldl (fun b j => if g j < g b then j else b) 0 = 0 := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih => simp [List.foldl_append, ih, not_lt.mpr (h a)]

/-- With every later factor at least `1`, `cumprod` is at least its first two. -/
theorem aux_linReachAdaptiveCora1D_varphiprod (φ : ℕ → ℝ) (h1 : ∀ i, 1 ≤ i → 1 ≤ φ i)
    (h0 : 0 ≤ φ 0) :
    ∀ j, 1 ≤ j → φ 0 * φ 1 ≤ ∏ i ∈ Finset.range (j + 1), φ i := by -- --- PROOF ---
  intro j hj
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Finset.prod_range_succ]
    · rw [Finset.prod_range_succ]
      have := ih hn
      have h1n := h1 (n + 1) (by omega)
      have : 0 ≤ φ 0 * φ 1 := mul_nonneg h0 (by linarith [h1 1 le_rfl])
      nlinarith

/-- `aux_optimaldeltat` from a point start (`rR = 0`) at `zetaP = 1` keeps the finite horizon when
the gain is at least `3`: no shorter step lowers the estimate. -/
theorem aux_linReachAdaptiveCora1D_optimal (rerr1 deltat varphimin : ℝ) (hr : 0 ≤ rerr1)
    (hd : deltat ≠ 0) (hv : 3 ≤ varphimin) :
    NonlinearSys.optimalDeltatCora 0 rerr1 deltat varphimin 1 (9 / 10) (5 / 10000)
      = deltat := by -- --- PROOF ---
  unfold NonlinearSys.optimalDeltatCora
  extract_lets dHused zetaZ kprimemax kprime k deltats floork varphimax varphi_h varphi varphiprod
    sumallbutlast objfuncset bestIdxnew
  have hk : ∀ j : ℕ, k j = (10 / 9 : ℝ) ^ j := by
    intro j; simp only [k, zpow_neg, zpow_natCast, ← inv_pow]; norm_num
  have hk1 : ∀ j, 1 ≤ k j := fun j => by rw [hk]; exact one_le_pow₀ (by norm_num)
  have hzZ : zetaZ = 1 / 4000 := by simp only [zetaZ, dHused]; norm_num
  -- every factor of `varphiprod` past the first is at least `1`
  have hφ : ∀ i : ℕ,
      varphi i = (varphimin * (9 / 10) ^ i + 9 / 10 * (1 - (9 / 10) ^ i)) / (9 / 10) := by
    intro i; simp only [varphi, deltats, varphi_h, varphimax]; field_simp; ring
  have hφ1 : ∀ i, 1 ≤ i → 1 ≤ varphi i := by
    intro i hi
    rw [hφ]
    have hp : (9 / 10 : ℝ) ^ i ≤ 9 / 10 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    have hp0 : 0 ≤ (9 / 10 : ℝ) ^ i := by positivity
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hφ0 : varphi 0 = varphimin / (9 / 10) := by rw [hφ]; simp
  have hφ1' : varphimin ≤ varphi 1 := by rw [hφ]; norm_num; linarith
  have hobj0 : objfuncset 0 = rerr1 * (varphimin / (9 / 10)) * (1 + 2 * zetaZ) := by
    simp only [objfuncset, sumallbutlast, varphiprod, floork, hk]
    simp [hφ0]
  -- no candidate beats the first
  have hobj : ∀ j, objfuncset 0 ≤ objfuncset j := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact le_rfl
    rw [hobj0]
    -- the sum is at least `⌊k⌋`
    have hsum : (floork j : ℝ) ≤ sumallbutlast j := by
      simp only [sumallbutlast, Real.one_rpow, mul_one]
      have : ∀ i ∈ Finset.Icc 1 (floork j), (1 : ℝ) ≤ (1 + 2 * zetaZ) ^ (k j + 1 - (i : ℝ)) := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        have : (i : ℝ) ≤ k j :=
          le_trans (by exact_mod_cast hi.2) (Nat.floor_le (by linarith [hk1 j]))
        exact Real.one_le_rpow (by rw [hzZ]; norm_num) (by linarith)
      calc (floork j : ℝ) = ∑ i ∈ Finset.Icc 1 (floork j), (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum this
    -- `⌊k⌋` is at least half of `k`, and the product at least `varphimin² / 0.9`
    have hfl : k j ≤ 2 * (floork j : ℝ) := by
      have h1 : (1 : ℝ) ≤ floork j := by exact_mod_cast Nat.one_le_floor_iff _ |>.mpr (hk1 j)
      have h2 := Nat.lt_floor_add_one (k j)
      simp only [floork]; simp only [floork] at h1; linarith
    have hextra : 0 ≤ (1 + zetaZ) ^ (k j - (j : ℝ)) * (k j - (floork j : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg (by rw [hzZ]; norm_num) _)
        (by simp only [floork]; linarith [Nat.floor_le (by linarith [hk1 j] : 0 ≤ k j)])
    have hprod : varphimin / (9 / 10) * varphimin ≤ varphiprod j := by
      have := aux_linReachAdaptiveCora1D_varphiprod varphi hφ1 (by rw [hφ0]; positivity) j hj
      rw [hφ0] at this
      have : varphimin / (9 / 10) * varphimin ≤ varphimin / (9 / 10) * varphi 1 :=
        mul_le_mul_of_nonneg_left hφ1' (by positivity)
      simp only [varphiprod]; linarith
    have hkpos : 0 < k j := by linarith [hk1 j]
    simp only [objfuncset, zero_mul, zero_add]
    -- rerr1 / k * prod * (sum + extra) ≥ rerr1 * prod * (floork / k) ≥ rerr1 * prod / 2
    have hA : varphimin / (9 / 10) * varphimin / 2 ≤ varphiprod j * (sumallbutlast j +
        (1 + zetaZ) ^ (k j - (j : ℝ)) * (k j - (floork j : ℝ))) / k j := by
      rw [le_div_iff₀ hkpos]
      have hpp : 0 ≤ varphiprod j := le_trans (by positivity) hprod
      have hS : k j / 2
          ≤ sumallbutlast j + (1 + zetaZ) ^ (k j - (j : ℝ)) * (k j - (floork j : ℝ)) := by
        have h4 : k j / 2 ≤ (floork j : ℝ) := by linarith
        exact le_trans h4 (le_trans (le_add_of_nonneg_right hextra) (add_le_add hsum le_rfl))
      calc varphimin / (9 / 10) * varphimin / 2 * k j
          = (varphimin / (9 / 10) * varphimin) * (k j / 2) := by ring
        _ ≤ varphiprod j * (k j / 2) := mul_le_mul_of_nonneg_right hprod (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hS hpp
    -- and `1 + 2 ζ_Z ≤ varphimin / 2`
    have hB : (1 + 2 * zetaZ) ≤ varphimin / 2 := by rw [hzZ]; linarith
    calc rerr1 * (varphimin / (9 / 10)) * (1 + 2 * zetaZ)
        ≤ rerr1 * (varphimin / (9 / 10) * varphimin / 2) := by
          rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hr
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ rerr1 * (varphiprod j * (sumallbutlast j +
        (1 + zetaZ) ^ (k j - (j : ℝ)) * (k j - (floork j : ℝ))) / k j) :=
          mul_le_mul_of_nonneg_left hA hr
      _ = rerr1 / k j * varphiprod j * (sumallbutlast j +
        (1 + zetaZ) ^ (k j - (j : ℝ)) * (k j - (floork j : ℝ))) := by ring
  have hb : bestIdxnew = 0 := aux_linReachAdaptiveCora1D_firstMin objfuncset hobj kprime
  simp only [hb, deltats, pow_zero, mul_one]

/-- `priv_abstractionError_adaptive` on a box whose shift by `p` has the Hessian bound `f''` at
its lower end. -/
theorem aux_linReachAdaptiveCora1D_abstrErr (f'' : ℝ → ℝ) (hessIv : ℝ → ℝ → Real.Interval ℝ)
    (hH : ∀ lo hi, lo ≤ hi → lo ≤ 0 → hi ≤ -lo →
      max |(hessIv lo hi).inf| |(hessIv lo hi).sup| = f'' lo)
    (p lo hi : ℝ) (h1 : lo + p ≤ hi + p) (h2 : lo + p ≤ 0)
    (h3 : hi + p ≤ -(lo + p)) : -- --- STMT ---
    NonlinearSys.abstrErrAdaptiveCora1D hessIv none p ⟨lo, hi⟩
      = 1 / 2 * max |lo| |hi| * f'' (lo + p) * max |lo| |hi| := by -- --- PROOF ---
  simp only [NonlinearSys.abstrErrAdaptiveCora1D, hH _ _ h1 h2 h3]

/-- A pass in closed form is monotone in the applied error. -/
theorem aux_linReachAdaptiveCora1D_mono (A B c u v : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (huv : u ≤ v) : -- --- STMT ---
    1 / 2 * (A + c * u) * (468559 / 7880 * (-(B + c * u)) ^ 4 - 122853 / 1970 * (-(B + c * u)) ^ 5)
        * (A + c * u) ≤
      1 / 2 * (A + c * v) * (468559 / 7880 * (-(B + c * v)) ^ 4
        - 122853 / 1970 * (-(B + c * v)) ^ 5) * (A + c * v) := by -- --- PROOF ---
  have e : ∀ y : ℝ, 468559 / 7880 * (-y) ^ 4 - 122853 / 1970 * (-y) ^ 5
      = 468559 / 7880 * y ^ 4 + 122853 / 1970 * y ^ 5 := fun y => by ring
  rw [e, e]
  have : c * u ≤ c * v := mul_le_mul_of_nonneg_left huv hc
  have : 0 ≤ c * u := mul_nonneg hc hu
  have : 0 ≤ c * v := by linarith
  gcongr

/-- The horizon run's numbers. -/
theorem aux_linReachAdaptiveCora1D_horizon (G : ℝ → ℝ)
    (hG : G = fun ae => 1 / 2 * (165961 / 165480 + 2 * ae)
      * (468559 / 7880 * (-(481 / 165480 + 2 * ae)) ^ 4
        - 122853 / 1970 * (-(481 / 165480 + 2 * ae)) ^ 5) * (165961 / 165480 + 2 * ae)) :
    0 < G 0 ∧ 11 / 10 * G 0 ≤ 3 / 10 ^ 9 ∧ G (3 / 10 ^ 9) ≤ 11 / 10 * G 0 ∧
      G (3 / 10 ^ 9) ≤ 22 / 10 ^ 10 := by -- --- PROOF ---
  subst hG
  norm_num

/-- The numbers of the runs at `0.9` times the horizon. -/
theorem aux_linReachAdaptiveCora1D_decr (G : ℝ → ℝ)
    (hG : G = fun ae => 1 / 2 * (2510328409443 / 2758000000000
      + 9 / 5 * ae) * (468559 / 7880 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 4
        - 122853 / 1970 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 5)
      * (2510328409443 / 2758000000000 + 9 / 5 * ae)) : -- --- STMT ---
    1 / 10 ^ 7 ≤ G 0 ∧ 11 / 10 * G 0 ≤ 297 / 10 ^ 9 ∧ G (9 / 10 * (22 / 10 ^ 10)) ≤ 27 / 10 ^ 8 ∧
      G (297 / 10 ^ 9) ≤ 11 / 10 * G 0 := by -- --- PROOF ---
  subst hG
  norm_num

/-- The horizon run's error loop settles on its second pass, below `2.2·10⁻⁹`. -/
theorem aux_linReachAdaptiveCora1D_horizonLoop (Φ : ℝ → ℝ)
    (hΦ : ∀ ae : ℝ, 0 ≤ ae → ae ≤ 1 / 1000 → Φ ae = 1 / 2 * (165961 / 165480 + 2 * ae)
      * (468559 / 7880 * (-(481 / 165480 + 2 * ae)) ^ 4
        - 122853 / 1970 * (-(481 / 165480 + 2 * ae)) ^ 5) * (165961 / 165480 + 2 * ae)) :
    ∃ eh, NonlinearSys.adaptErrLoopCora1D Φ 2 1 0 0 = some eh ∧ 0 < eh ∧
      eh ≤ 22 / 10 ^ 10 := by -- --- PROOF ---
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun ae => 1 / 2 * (165961 / 165480 + 2 * ae)
      * (468559 / 7880 * (-(481 / 165480 + 2 * ae)) ^ 4
        - 122853 / 1970 * (-(481 / 165480 + 2 * ae)) ^ 5) * (165961 / 165480 + 2 * ae) := ⟨_, rfl⟩
  have hΦG : ∀ ae : ℝ, 0 ≤ ae → ae ≤ 1 / 1000 → Φ ae = G ae := fun ae h0 h1 => by
    rw [hΦ ae h0 h1, hG]
  have hmono : ∀ u v, 0 ≤ u → u ≤ v → G u ≤ G v := fun u v hu huv => by
    rw [hG]
    exact aux_linReachAdaptiveCora1D_mono _ _ 2 u v (by norm_num) (by norm_num) (by norm_num) hu
      huv
  -- the first pass does not fit, the second does
  obtain ⟨hG0, hG0', hG3, hG3'⟩ := aux_linReachAdaptiveCora1D_horizon G hG
  have e0 : Φ 0 = G 0 := hΦG 0 le_rfl (by norm_num)
  have e1 : Φ (11 / 10 * G 0) = G (11 / 10 * G 0) :=
    hΦG _ (by linarith only [hG0]) (by linarith only [hG0'])
  have hup := hmono _ _ (by linarith only [hG0]) hG0'
  have hlo := hmono 0 (11 / 10 * G 0) le_rfl (by linarith only [hG0])
  refine ⟨G (11 / 10 * G 0), ?_, by linarith only [hG0, hlo], by linarith only [hup, hG3']⟩
  have := aux_linReachAdaptiveCora1D_loop Φ 0 0 0 (by rw [e0]; exact hG0)
    (by rw [e0, e1]; linarith only [hup, hG3])
  rwa [e0, e1] at this

/-- The first run at `0.9` times the horizon, from `0.9` times the horizon's error, settles on
its second pass, above `10⁻⁷`. -/
theorem aux_linReachAdaptiveCora1D_decrLoop (Φ : ℝ → ℝ)
    (hΦ : ∀ ae : ℝ, 0 ≤ ae → ae ≤ 1 / 1000 → Φ ae = 1 / 2 * (2510328409443 / 2758000000000
      + 9 / 5 * ae) * (468559 / 7880 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 4
        - 122853 / 1970 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 5)
      * (2510328409443 / 2758000000000 + 9 / 5 * ae))
    (eh : ℝ) (h0 : 0 ≤ eh) (h1 : eh ≤ 22 / 10 ^ 10) : -- --- STMT ---
    ∃ e, NonlinearSys.adaptErrLoopCora1D Φ 2 1 (9 / 10 * eh) 0 = some e ∧
      1 / 10 ^ 7 ≤ e := by -- --- PROOF ---
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun ae => 1 / 2 * (2510328409443 / 2758000000000
      + 9 / 5 * ae) * (468559 / 7880 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 4
        - 122853 / 1970 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 5)
      * (2510328409443 / 2758000000000 + 9 / 5 * ae) := ⟨_, rfl⟩
  have hΦG : ∀ ae : ℝ, 0 ≤ ae → ae ≤ 1 / 1000 → Φ ae = G ae := fun ae h0 h1 => by
    rw [hΦ ae h0 h1, hG]
  have hmono : ∀ u v, 0 ≤ u → u ≤ v → G u ≤ G v := fun u v hu huv => by
    rw [hG]
    exact aux_linReachAdaptiveCora1D_mono _ _ (9 / 5) u v (by norm_num) (by norm_num) (by norm_num)
      hu huv
  -- the first pass does not fit, the second does
  obtain ⟨hG0, hG0', hGa, hGb⟩ := aux_linReachAdaptiveCora1D_decr G hG
  have ht0 := hmono 0 (9 / 10 * eh) le_rfl (by linarith only [h0])
  have ht1 := hmono (9 / 10 * eh) (9 / 10 * (22 / 10 ^ 10)) (by linarith only [h0])
    (by linarith only [h1])
  have e0 : Φ (9 / 10 * eh) = G (9 / 10 * eh) :=
    hΦG _ (by linarith only [h0]) (by linarith only [h1])
  have e1 : Φ (11 / 10 * G (9 / 10 * eh)) = G (11 / 10 * G (9 / 10 * eh)) :=
    hΦG _ (by linarith only [hG0, ht0]) (by linarith only [ht1, hGa])
  have hup := hmono (11 / 10 * G (9 / 10 * eh)) (297 / 10 ^ 9) (by linarith only [hG0, ht0])
    (by linarith only [ht1, hGa])
  have hlo := hmono 0 (11 / 10 * G (9 / 10 * eh)) le_rfl (by linarith only [hG0, ht0])
  refine ⟨G (11 / 10 * G (9 / 10 * eh)), ?_, by linarith only [hG0, hlo]⟩
  have := aux_linReachAdaptiveCora1D_loop Φ (9 / 10 * eh) 0 0
    (by rw [e0]; linarith only [h1, hG0, ht0]) (by rw [e0, e1]; linarith only [hup, hGb, ht0])
  rwa [e0, e1] at this

/-- The second run at `0.9` times the horizon, from `0`, settles on its second pass. -/
theorem aux_linReachAdaptiveCora1D_decrLoop₀ (Φ : ℝ → ℝ)
    (hΦ : ∀ ae : ℝ, 0 ≤ ae → ae ≤ 1 / 1000 → Φ ae = 1 / 2 * (2510328409443 / 2758000000000
      + 9 / 5 * ae) * (468559 / 7880 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 4
        - 122853 / 1970 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 5)
      * (2510328409443 / 2758000000000 + 9 / 5 * ae)) : -- --- STMT ---
    ∃ e, NonlinearSys.adaptErrLoopCora1D Φ 2 1 0 0 = some e := by -- --- PROOF ---
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun ae => 1 / 2 * (2510328409443 / 2758000000000
      + 9 / 5 * ae) * (468559 / 7880 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 4
        - 122853 / 1970 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 5)
      * (2510328409443 / 2758000000000 + 9 / 5 * ae) := ⟨_, rfl⟩
  have hΦG : ∀ ae : ℝ, 0 ≤ ae → ae ≤ 1 / 1000 → Φ ae = G ae := fun ae h0 h1 => by
    rw [hΦ ae h0 h1, hG]
  have hmono : ∀ u v, 0 ≤ u → u ≤ v → G u ≤ G v := fun u v hu huv => by
    rw [hG]
    exact aux_linReachAdaptiveCora1D_mono _ _ (9 / 5) u v (by norm_num) (by norm_num) (by norm_num)
      hu huv
  -- the first pass does not fit, the second does
  obtain ⟨hG0, hG0', hGa, hGb⟩ := aux_linReachAdaptiveCora1D_decr G hG
  have e0 : Φ 0 = G 0 := hΦG 0 le_rfl (by norm_num)
  have e1 : Φ (11 / 10 * G 0) = G (11 / 10 * G 0) :=
    hΦG _ (by linarith only [hG0]) (by linarith only [hG0'])
  have hup := hmono (11 / 10 * G 0) (297 / 10 ^ 9) (by linarith only [hG0]) hG0'
  exact ⟨_, aux_linReachAdaptiveCora1D_loop Φ 0 0 0 (by rw [e0]; linarith only [hG0])
    (by rw [e0, e1]; linarith only [hup, hGb])⟩

-- the step's three runs are unfolded and evaluated in one declaration, over their shared lets
set_option maxHeartbeats 100000 in
/-- CORA's first adaptive step on the example: the tuned step is the horizon, and `Rti` ends
below `1/50000`. -/
theorem aux_linReachAdaptiveCora1D_step (hessIv : ℝ → ℝ → Real.Interval ℝ)
    (hH : ∀ lo hi, lo ≤ hi → lo ≤ 0 → hi ≤ -lo → max |(hessIv lo hi).inf| |(hessIv lo hi).sup|
      = (fun x : ℝ => 468559 / 7880 * x ^ 4 - 122853 / 1970 * x ^ 5) lo) : -- --- STMT ---
    ∃ R, NonlinearSys.linReachAdaptiveCora1D
      (fun x : ℝ => 1 - 59049 / 39400 * x + 468559 / 236400 * x ^ 6 - 40951 / 27580 * x ^ 7)
      (fun x => -(59049 / 39400) + 468559 / 39400 * x ^ 5 - 40951 / 3940 * x ^ 6)
      hessIv 0 0 200 2 = some R ∧ R.2.2 = 2 ∧ R.1.sup < 1 / 50000 := by -- --- PROOF ---
  unfold NonlinearSys.linReachAdaptiveCora1D
  extract_lets decrFactor redFactor zetaphi timeStep_h finitehorizon p_h f0_h A_h zetaP_h Rdelta_h
    Rlintp_h Rlinti_h totalInt₀ H₀ c₀ r₀ H_test hessianConst Φ_h timeStep₁ p₁ f0₁ A₁ Rdelta₁
    Rlintp₁ Rlinti₁ Φ₁
  -- the horizon run
  have hts : timeStep_h = 2 := by simp only [timeStep_h]; norm_num
  have hfh : finitehorizon = 2 := hts
  have hp : p_h = 1 := by simp only [p_h, hts]; norm_num
  have hA : A_h = 0 := by simp only [A_h, hp]; norm_num
  have hzP : zetaP_h = 1 := by simp only [zetaP_h, hA, zero_mul, Real.exp_zero]
  have hRl : Rlinti_h = ⟨-165961 / 165480, -1⟩ := by
    simp only [Rlinti_h, Rdelta_h, Rlintp_h, f0_h, hp, hts]; norm_num
  have hRtp : Rlintp_h = -165961 / 165480 := by
    simp only [Rlintp_h, Rdelta_h, f0_h, hp, hts]; norm_num
  -- the first box and its enlargement read different Hessians: not constant
  have hH₀ : max |H₀.inf| |H₀.sup| = 468559 / 7880 * (-481 / 165480) ^ 4
      - 122853 / 1970 * (-481 / 165480) ^ 5 := by
    have e : H₀ = hessIv (-481 / 165480) 0 := by
      simp only [H₀, totalInt₀, hRl, hp]; norm_num
    rw [e, hH _ _ (by norm_num) (by norm_num) (by norm_num)]
  have hHt : max |H_test.inf| |H_test.sup| = 468559 / 7880 * (-10101 / 3309600) ^ 4
      - 122853 / 1970 * (-10101 / 3309600) ^ 5 := by
    have e : H_test = hessIv (-10101 / 3309600) (481 / 3309600) := by
      simp only [H_test, c₀, r₀, totalInt₀, hRl, hp]; norm_num
    rw [e, hH _ _ (by norm_num) (by norm_num) (by norm_num)]
  have hhc : hessianConst = none := by
    simp only [hessianConst]
    rw [if_neg]
    intro h
    have := hH₀
    rw [h.1, h.2, hHt] at this
    norm_num at this
  -- a pass of the horizon run, in closed form
  have hΦh : ∀ ae : ℝ, 0 ≤ ae → ae ≤ 1 / 1000 → Φ_h ae = 1 / 2 * (165961 / 165480 + 2 * ae)
      * (468559 / 7880 * (-(481 / 165480 + 2 * ae)) ^ 4
        - 122853 / 1970 * (-(481 / 165480 + 2 * ae)) ^ 5) * (165961 / 165480 + 2 * ae) := by
    intro ae h0 h1
    simp only [Φ_h, hhc, hRl, hp, hts]
    rw [aux_linReachAdaptiveCora1D_abstrErr _ hessIv hH 1 _ _ (by linarith)
      (by linarith) (by linarith)]
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith), max_eq_left (by linarith)]
    ring_nf
  obtain ⟨eh, hloop_h, heh_pos, heh1⟩ := aux_linReachAdaptiveCora1D_horizonLoop Φ_h hΦh
  rw [if_neg (not_not.mpr hA), hloop_h]
  dsimp (config := { zeta := false }) only
  rw [if_neg heh_pos.ne']
  extract_lets Rerror_h abstrerr_h error_adm₁
  -- the run at `0.9` times the horizon
  have hts₁ : timeStep₁ = 9 / 5 := by simp only [timeStep₁, decrFactor, hts]; norm_num
  have hp₁ : p₁ = 9 / 10 := by simp only [p₁, hts₁]; norm_num
  have hA₁ : A₁ = 0 := by simp only [A₁, hp₁]; norm_num
  -- its linearized run and a pass, in closed form
  have hRl₁ : Rlinti₁ = ⟨-2510328409443 / 2758000000000, -9 / 10⟩ := by
    simp only [Rlinti₁, Rdelta₁, Rlintp₁, f0₁, hp₁, hts₁]; norm_num
  have hΦ₁ : ∀ ae : ℝ, 0 ≤ ae → ae ≤ 1 / 1000 → Φ₁ ae = 1 / 2 * (2510328409443 / 2758000000000
      + 9 / 5 * ae) * (468559 / 7880 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 4
        - 122853 / 1970 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 5)
      * (2510328409443 / 2758000000000 + 9 / 5 * ae) := by
    intro ae h0 h1
    simp only [Φ₁, hhc, hRl₁, hp₁, hts₁]
    rw [aux_linReachAdaptiveCora1D_abstrErr _ hessIv hH (9 / 10) _ _ (by linarith)
      (by linarith) (by linarith)]
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith), max_eq_left (by linarith)]
    ring_nf
  obtain ⟨e₁, hloop₁, he₁⟩ := aux_linReachAdaptiveCora1D_decrLoop Φ₁ hΦ₁ eh heh_pos.le heh1
  rw [if_neg (not_not.mpr hA₁), hloop₁]
  dsimp (config := { zeta := false }) only
  extract_lets abstrerr₁ varphi timeStep₂ timeStep₃ p₃ f0₃ A₃ Rdelta₃ Rlintp₃ Rlinti₃ Φ₃
  -- the gain of the two runs, and the tuned time step
  have hvarphi : 3 ≤ varphi := by
    show 3 ≤ timeStep₁ * e₁ / (timeStep_h * eh)
    rw [hts₁, hts, le_div_iff₀ (by positivity)]
    linarith only [he₁, heh1]
  rw [if_neg (not_lt.mpr (le_trans (by norm_num) hvarphi : (68 / 100 : ℝ) ≤ varphi))]
  have hopt : timeStep₂ = finitehorizon := by
    show NonlinearSys.optimalDeltatCora 0 (timeStep_h * eh) finitehorizon varphi zetaP_h (9 / 10)
      (5 / 10000) = finitehorizon
    rw [hzP]
    exact aux_linReachAdaptiveCora1D_optimal _ _ _ (by rw [hts]; linarith only [heh_pos])
      (by rw [hfh]; norm_num) hvarphi
  rw [if_neg (not_not.mpr hopt)]
  -- run 2, at `0.9` times the horizon again
  have hts₃ : timeStep₃ = 9 / 5 := by
    show timeStep₂ * (9 / 10) = 9 / 5
    rw [hopt, hfh]; norm_num
  have hp₃ : p₃ = 9 / 10 := by simp only [p₃, hts₃]; norm_num
  have hA₃ : A₃ = 0 := by simp only [A₃, hp₃]; norm_num
  -- its linearized run and a pass, in closed form
  have hRl₃ : Rlinti₃ = ⟨-2510328409443 / 2758000000000, -9 / 10⟩ := by
    simp only [Rlinti₃, Rdelta₃, Rlintp₃, f0₃, hp₃, hts₃]; norm_num
  have hΦ₃ : ∀ ae : ℝ, 0 ≤ ae → ae ≤ 1 / 1000 → Φ₃ ae = 1 / 2 * (2510328409443 / 2758000000000
      + 9 / 5 * ae) * (468559 / 7880 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 4
        - 122853 / 1970 * (-(28128409443 / 2758000000000 + 9 / 5 * ae)) ^ 5)
      * (2510328409443 / 2758000000000 + 9 / 5 * ae) := by
    intro ae h0 h1
    simp only [Φ₃, hhc, hRl₃, hp₃, hts₃]
    rw [aux_linReachAdaptiveCora1D_abstrErr _ hessIv hH (9 / 10) _ _ (by linarith)
      (by linarith) (by linarith)]
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith), max_eq_left (by linarith)]
    ring_nf
  -- it settles, and the step returns the horizon run's sets
  obtain ⟨e₃, hloop₃⟩ := aux_linReachAdaptiveCora1D_decrLoop₀ Φ₃ hΦ₃
  rw [if_neg (not_not.mpr hA₃), hloop₃]
  dsimp (config := { zeta := false }) only
  refine ⟨_, rfl, hfh, ?_⟩
  show Rlinti_h.sup + p_h + timeStep_h * eh < 1 / 50000
  rw [hRl, hp, hts]
  linarith only [heh1]

/-- A run of `ẋ = f(x)` from `0` on `[0, 1/4]` that is at least `1/20` at its end. -/
theorem aux_linReachAdaptiveCora1D_run (f f' : ℝ → ℝ)
    (hfd : f = fun x : ℝ => 1 - 59049 / 39400 * x + 468559 / 236400 * x ^ 6
      - 40951 / 27580 * x ^ 7)
    (hf'd : f' = fun x : ℝ => -(59049 / 39400) + 468559 / 39400 * x ^ 5 - 40951 / 3940 * x ^ 6)
    (hf : ∀ x, HasDerivAt f (f' x) x) : -- --- STMT ---
    ∃ x : ℝ → ℝ, x 0 = 0 ∧
        (∀ t ∈ Icc (0 : ℝ) (1 / 4), HasDerivWithinAt x (f (x t)) (Icc 0 (1 / 4)) t) ∧
        1 / 20 ≤ x (1 / 4) := by -- --- PROOF ---
  -- Picard-Lindelöf on `[0, 1/4]` in the ball `|x| ≤ 1/2`, where `|f| ≤ 2` and `|f'| ≤ 3`
  have hball : ∀ x ∈ closedBall (0 : ℝ) ((1 / 2 : ℝ≥0) : ℝ), -(1 / 2) ≤ x ∧ x ≤ 1 / 2 := by
    intro x hx
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx
    norm_num at hx
    exact abs_le.mp hx
  -- the powers of a point of the ball
  have hpow : ∀ x : ℝ, -(1 / 2) ≤ x → x ≤ 1 / 2 → ∀ n : ℕ,
      -(1 / 2) ^ n ≤ x ^ n ∧ x ^ n ≤ (1 / 2) ^ n := by
    intro x h1 h2 n
    have hx : |x| ≤ 1 / 2 := abs_le.mpr ⟨h1, h2⟩
    have := pow_le_pow_left₀ (abs_nonneg x) hx n
    rw [← abs_pow] at this
    exact abs_le.mp this
  have hlip : LipschitzOnWith 3 f (closedBall (0 : ℝ) ((1 / 2 : ℝ≥0) : ℝ)) := by
    refine (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (hf x).hasDerivWithinAt) fun x hx => ?_
    obtain ⟨h1, h2⟩ := hball x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, hf'd]
    simp only [NNReal.coe_ofNat]
    obtain ⟨h5, h5'⟩ := hpow x h1 h2 5
    obtain ⟨h6, h6'⟩ := hpow x h1 h2 6
    rw [abs_le]
    constructor <;> norm_num at h5 h5' h6 h6' ⊢ <;> nlinarith
  -- `|f| ≤ 2` on the ball and `2 · 1/4 ≤ 1/2`
  have hpl : IsPicardLindelof (fun _ : ℝ => f) (⟨0, by norm_num⟩ : Icc (0 : ℝ) (1 / 4)) (0 : ℝ)
      (1 / 2) 0 2 3 := by
    refine ⟨fun _ _ => hlip, fun _ _ => continuousOn_const, fun _ _ x hx => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hball x hx
      rw [Real.norm_eq_abs, hfd]
      simp only [NNReal.coe_ofNat]
      obtain ⟨h6, h6'⟩ := hpow x h1 h2 6
      obtain ⟨h7, h7'⟩ := hpow x h1 h2 7
      rw [abs_le]
      constructor <;> norm_num at h6 h6' h7 h7' ⊢ <;> nlinarith
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
      obtain ⟨_, h7'⟩ := hpow _ h1 h2 7
      generalize α.compProj t = y at h1 h2 h7' ⊢
      have h6 : 0 ≤ y ^ 6 := by positivity
      simp only [hfd]
      norm_num at h7'
      linarith
  have := hmono ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num : (0 : ℝ) ≤ 1 / 4)
  simp only [h0] at this
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's adaptive `'lin'` step for `ẋ = f(x)` from `{0}`, `tFinal = 200`, at any interval Hessian
of magnitude `f''(lo)` where `M` is exact, tunes its first step to `Δt = 2` and returns an `Rti`
ending below `1/50000`; a run from `0` is at `x(1/4) ≥ 1/20`. -/
theorem NonlinearSys.linReachAdaptiveCora1D_hessianRegion_counterexample : -- --- STMT ---
    let f : ℝ → ℝ := fun x => 1 - 59049 / 39400 * x + 468559 / 236400 * x ^ 6
      - 40951 / 27580 * x ^ 7
    let f' : ℝ → ℝ := fun x => -(59049 / 39400) + 468559 / 39400 * x ^ 5 - 40951 / 3940 * x ^ 6
    let f'' : ℝ → ℝ := fun x => 468559 / 7880 * x ^ 4 - 122853 / 1970 * x ^ 5
    let M : ℝ → ℝ → ℝ := fun lo hi =>
      468559 / 7880 * max |lo| |hi| ^ 4 + 122853 / 1970 * max |lo| |hi| ^ 5
    (∀ x, HasDerivAt f (f' x) x) ∧ (∀ x, HasDerivAt f' (f'' x) x) ∧
      (∀ lo hi y, y ∈ Icc lo hi → |f'' y| ≤ M lo hi) ∧
      (∀ lo hi, lo ≤ hi → lo ≤ 0 → hi ≤ -lo → M lo hi = f'' lo) ∧
      (∀ hessIv : ℝ → ℝ → Real.Interval ℝ, (∀ lo hi, lo ≤ hi → lo ≤ 0 → hi ≤ -lo →
          max |(hessIv lo hi).inf| |(hessIv lo hi).sup| = f'' lo) →
        ∃ R, NonlinearSys.linReachAdaptiveCora1D f f' hessIv 0 0 200 2 = some R ∧
          R.2.2 = 2 ∧ R.1.sup < 1 / 50000) ∧
      ∃ x : ℝ → ℝ, x 0 = 0 ∧
        (∀ t ∈ Icc (0 : ℝ) (1 / 4), HasDerivWithinAt x (f (x t)) (Icc 0 (1 / 4)) t) ∧
        1 / 20 ≤ x (1 / 4) := by -- --- PROOF ---
  intro f f' f'' M
  -- the derivatives of the polynomial
  have hf : ∀ x, HasDerivAt f (f' x) x := fun x =>
    (((((hasDerivAt_id' x).const_mul (59049 / 39400 : ℝ)).const_sub 1).add
      ((hasDerivAt_pow 6 x).const_mul (468559 / 236400 : ℝ))).sub
      ((hasDerivAt_pow 7 x).const_mul (40951 / 27580 : ℝ))).congr_deriv (by norm_num; ring)
  have hf' : ∀ x, HasDerivAt f' (f'' x) x := fun x =>
    ((((hasDerivAt_pow 5 x).const_mul (468559 / 39400 : ℝ)).const_add (-(59049 / 39400))).sub
      ((hasDerivAt_pow 6 x).const_mul (40951 / 3940 : ℝ))).congr_deriv (by norm_num; ring)
  refine ⟨hf, hf', ?_, ?_, fun hessIv hH => aux_linReachAdaptiveCora1D_step hessIv hH,
    aux_linReachAdaptiveCora1D_run f f' rfl rfl hf⟩
  -- `|f''(y)|` is at most its monomials' magnitudes at the larger end point
  · intro lo hi y hy
    have hm : |y| ≤ max |lo| |hi| := by
      rcases le_total 0 y with h0 | h0
      · rw [abs_of_nonneg h0]
        exact le_max_of_le_right (le_trans hy.2 (le_abs_self _))
      · rw [abs_of_nonpos h0]
        exact le_max_of_le_left (le_trans (neg_le_neg hy.1) (neg_le_abs _))
    have h4 : |y| ^ 4 ≤ max |lo| |hi| ^ 4 := pow_le_pow_left₀ (abs_nonneg y) hm 4
    have h5 : |y| ^ 5 ≤ max |lo| |hi| ^ 5 := pow_le_pow_left₀ (abs_nonneg y) hm 5
    calc |f'' y| ≤ |468559 / 7880 * y ^ 4| + |122853 / 1970 * y ^ 5| := abs_sub _ _
      _ = 468559 / 7880 * |y| ^ 4 + 122853 / 1970 * |y| ^ 5 := by
        rw [abs_mul, abs_mul, abs_pow, abs_pow]; norm_num
      _ ≤ M lo hi := by simp only [M]; gcongr
  -- on a box `[lo, hi]` with `lo ≤ 0`, `hi ≤ -lo`, the larger end is `lo`, where both agree
  · intro lo hi h1 h2 h3
    have hm : max |lo| |hi| = -lo := by
      rw [abs_of_nonpos h2]
      exact max_eq_left (abs_le.mpr ⟨by linarith, h3⟩)
    simp only [M, f'', hm]
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
