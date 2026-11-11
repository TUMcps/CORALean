module

public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachPolyAdaptiveOptions
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptiveOrdersFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPolyAdaptivePassFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.OptimalDeltatAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.VarphiEstFloat
public import CORALean.Global.Float.RatUp

@[expose] public section

/-!
# CORA's `linReach_adaptive` at `'poly'`, repaired, in floats

One step of `@nonlinearSys/linReach_adaptive.m` at `alg = 'poly'` (tensor order 3), CORA's
structure and tuning as in [1, Alg. 2]: the finite horizon from the last gain (enlarged by `1.1`
within `1e-3` of the last step size), `polyGain` (one order lost at the second step when the
third-order tensor is empty) and the outer loop: a pass, halved when its error loop fails;
`aux_getPowers`; a run at the horizon giving `aux_optimaldeltat` with `dHused = 0.3`; a run at that
step size whose gain `aux_varphiest` estimates over all dimensions; the horizon's sets when the two
coincide. There is no tensor order to tune. Every set is a pass's at its own step size; CORA's
caches (`gredIdx`, `tt_*`) are omitted.

## Inputs
* `fm` – float Hessian model
* `U` – input zonotope
* `o` – adaptive options
* `st` – state after the last step

## Output
* the state after the step, with the step's unreduced sets, or none

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- CORA's `withinTol(a, b, tol)`: absolutely or relatively within `tol`. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat]
def step_withinTolPoly (a b tol : 𝕋) : Bool :=
  let d := absolute (subUp a b)
  le d tol || le (divUp d (minimum (absolute a) (absolute b))) tol

/-- `zeroWidthDim`: the dimensions whose generators sum to at most `tol` in magnitude. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat]
def step_zeroWidthDimPoly (R : PolyZonotope (Vec 𝕋 n)) (tol : 𝕋) : Fin n → Bool :=
  fun i => le (sumUp fun j => absolute (R.zonotopeEven.G j i)) tol  -- withinTol(sum(abs(G),2),0)

/-- `min(orders)`, the finite ones; `0` if all are `Inf`. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat]
def step_minorderPoly (orders : Fin n → Option ℕ) : ℕ :=
  ((List.finRange n).filterMap orders).foldl min ((List.finRange n).filterMap orders |>.headD 0)

/-- `max(errRatio(~isnan(errRatio)))` over the dimensions in `mask`, `0/0` skipped. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat]
def step_maxRatioPoly (mask : Fin n → Bool) (num den : Vec 𝕋 n) : 𝕋 :=
  maximumOver fun i => if mask i && !(le (num i) zero && le (den i) zero)
    then divUp (num i) (den i) else zero

/-- `rad(interval(R))`, the radius of the interval hull. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat]
def step_radHullPoly (R : PolyZonotope (Vec 𝕋 n)) : Vec 𝕋 n :=
  fun i => half (subUp (R.zonotopeEven.interval.sup i) (R.zonotopeEven.interval.inf i))

/-- `options` after a pass: the zero-width dimensions and, when they changed (or at the very
first pass), the orders `q_i` of the abstraction error (`aux_getPowers`, `sigma + 1` if the third-
order tensor is empty). -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_adaptiveOrdersPoly (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋)
    (L : NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n)
    (P : NonlinearSys.LinReachPolyAdaptivePass 𝕋 n) :
    NonlinearSys.LinReachPolyAdaptiveState 𝕋 n :=
  let zw := step_zeroWidthDimPoly L.st.R o.zeroTol
  let orders := NonlinearSys.adaptiveOrdersFloat P.A zw P.Gzero      -- aux_getPowers
    (fm.hess (Interval.point P.xs) (Interval.point U.c)) 100 (if o.thirdOrderEmpty then 1 else 0)
  if L.veryfirststep ∨ ∃ i, zw i ≠ L.st.zeroWidthDim i              -- rank of Rstart changes
  then { L.st with zeroWidthDim := zw, orders := orders, minorder := step_minorderPoly orders }
  else L.st

/-- `zetaP`: `exp(trace(A*timeStep))` at the first run, else as it was. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat]
def step_adaptiveZetaPPoly (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋)
    (L : NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n)
    (P : NonlinearSys.LinReachPolyAdaptivePass 𝕋 n) : 𝕋 :=
  if L.run = 1 then expUp o.prec (sumUp fun i => mulUp (P.A i i) L.timeStep) else L.zetaP

/-- The first run (at the horizon) after a pass: the locals the loop continues with, `run` set
to `0` where CORA's `continue` skips the run counter. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_adaptiveHorizonPoly (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋)
    (L : NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n)
    (P : NonlinearSys.LinReachPolyAdaptivePass 𝕋 n) :
    NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n :=
  let decr := o.decrFactor
  let zetaP := step_adaptiveZetaPPoly o L P
  let st := fm.step_adaptiveOrdersPoly U o L P
  let mask := fun i => decide (st.orders i = some st.minorder)      -- orders == minorder
  let zetaphi := o.zetaphi ⟨min st.minorder 2, by omega⟩             -- zetaphi(minorder+1)
  let hor := (L.hor.map (·.2)).getD P                               -- Rerror_h
  let rR := normUp o.prec (step_radHullPoly st.R)                   -- vecnorm(rad(interval(Rt)))
  let decrErr := fun i => mulUp decr (P.trueError i)                -- decrFactor * trueError
  let dH := some o.dHused                                           -- 0.3
  if st.i = 1 then
    if L.veryfirststep then                                         -- save, decrease, again
      { L with
        st := st, veryfirststep := false, zetaP := zetaP, zetaPh := zetaP,
        hor := some (L.timeStep, P), timeStep := mulUp decr L.timeStep, errAdm := decrErr,
        run := 0 }
    else
      let varphi := step_maxRatioPoly mask P.abstrerr hor.abstrerr  -- max(errRatio)
      if le zetaphi varphi = false then                             -- varphi < zetaphi
        { L with
          st := st, zetaP := zetaP, zetaPh := zetaP, hor := some (L.timeStep, P),
          finitehorizon := L.timeStep, timeStep := mulUp decr L.timeStep, errAdm := decrErr,
          run := 0 }
      else
        { L with
          st := { st with
            varphi := varphi, finitehorizon := L.finitehorizon, errAdmHorizon := P.trueError },
          zetaP := zetaP,
          timeStep := NonlinearSys.optimalDeltatAdaptiveFloat o.prec decr o.redFactor rR
            (normUp o.prec hor.abstrerr) L.finitehorizon varphi L.zetaPh dH,  -- aux_optimaldeltat
          errAdm := fun _ => zero }
  else
    let Δt := NonlinearSys.optimalDeltatAdaptiveFloat o.prec decr o.redFactor rR
      (normUp o.prec P.abstrerr) L.finitehorizon st.varphi zetaP dH  -- aux_optimaldeltat
    { L with
      st := { st with errAdmHorizon := P.trueError },
      zetaP := zetaP, hor := some (L.timeStep, P), errAdm := st.errAdmDeltatopt,
      timeStep := if ToRat.toRat Δt ≤ o.tFinal - st.t then Δt else ratUp (o.tFinal - st.t) }

/-- The second run (at the tuned step size), or the last step's only one: the locals the loop
ends on, with the gain and the errors of the next step. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_adaptiveFinishPoly (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋)
    (L : NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n)
    (P : NonlinearSys.LinReachPolyAdaptivePass 𝕋 n) :
    NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n :=
  let st := fm.step_adaptiveOrdersPoly U o L P
  let mask := fun i => decide (st.orders i = some st.minorder)      -- orders == minorder
  let hor := (L.hor.map (·.2)).getD P                               -- Rerror_h
  let varphi := if L.timeStepequalHorizon then step_maxRatioPoly mask P.abstrerr hor.abstrerr
    else if L.lastStep = false then
      NonlinearSys.varphiEstFloat o.prec L.finitehorizon L.timeStep hor.abstrerr P.abstrerr
        o.decrFactor (fun _ => true) st.minorder o.varphiTol o.varphiStep o.fuel  -- aux_varphiest
    else st.varphi
  let st : NonlinearSys.LinReachPolyAdaptiveState 𝕋 n := { st with
    varphi := varphi, finitehorizon := L.finitehorizon, errAdmDeltatopt := P.trueError }
  { L with st := st, zetaP := step_adaptiveZetaPPoly o L P }

/-- What the outer loop does after a pass `P` at `L.timeStep`: `inl` the locals it continues
with (the run counter advanced, and the horizon test), `inr` the locals it ends on. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_linReachPolyAdaptiveDecide
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (U : Zonotope (Vec 𝕋 m))
    (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋) (L : NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n)
    (P : NonlinearSys.LinReachPolyAdaptivePass 𝕋 n) :
    NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n ⊕ NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n :=
  if L.run = 1 ∧ L.lastStep = false then
    let L₁ := fm.step_adaptiveHorizonPoly U o L P                   -- run using finite horizon
    if L₁.run = 0 then .inl { L₁ with run := 1 }                    -- continue
    else if le L₁.timeStep L₁.finitehorizon && le L₁.finitehorizon L₁.timeStep then
      .inl { L₁ with                                                -- timeStepequalHorizon
        run := L₁.run + 1, timeStepequalHorizon := true,
        timeStep := mulUp L₁.timeStep o.decrFactor }
    else .inl { L₁ with run := L₁.run + 1 }
  else .inr (fm.step_adaptiveFinishPoly U o L P)                    -- second run: break

/-- The outer `while true` loop of the step: a pass at the current step size, halved when it
fails, and what `step_linReachPolyAdaptiveDecide` makes of it; the locals and the pass it ends on,
or none once `fuel` runs out. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_linReachPolyAdaptiveLoop
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (U : Zonotope (Vec 𝕋 m))
    (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋) :
    ℕ → NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n →
      Option (NonlinearSys.LinReachPolyAdaptiveLoop 𝕋 n ×
        NonlinearSys.LinReachPolyAdaptivePass 𝕋 n)
  | 0, _ => none
  | fuel + 1, L =>
    match fm.linReachPolyAdaptivePassFloat U ⟨⟨L.timeStep, o.taylorTerms⟩, o.zonotopeOrder⟩
      o.enlarge o.redFactor o.prec o.fuel L.st.R L.errAdm with
    | none =>                                                       -- ~Lconverged: halve
      fm.step_linReachPolyAdaptiveLoop U o fuel { L with
        timeStep := half L.timeStep, finitehorizon := half L.timeStep,
        errAdm := L.st.errAdmHorizon }
    | some P =>
      match fm.step_linReachPolyAdaptiveDecide U o L P with
      | .inl L₁ => fm.step_linReachPolyAdaptiveLoop U o fuel L₁     -- continue
      | .inr L₂ => some (L₂, P)                                     -- break


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One step of CORA's `linReach_adaptive` at `'poly'` from `st`: the state after it, its sets
unreduced, or none if its loop runs out of `fuel`. -/
def NonlinearSys.FloatHessModel.linReachPolyAdaptiveFloat
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (U : Zonotope (Vec 𝕋 m))
    (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋)
    (st : NonlinearSys.LinReachPolyAdaptiveState 𝕋 n) :
    Option (NonlinearSys.LinReachPolyAdaptiveState 𝕋 n) := do
  let rem := o.tFinal - st.t                                        -- tFinal - options.t
  let zetaphi := o.zetaphi ⟨min st.minorder 2, by omega⟩
  let fh := mulUp st.finitehorizon (subUp (addUp one st.varphi) zetaphi)  -- finitehorizon
  let h₀ : 𝕋 × Bool × Bool :=                                       -- timeStep, last, first
    if st.i = 1 then (mulUp (ratUp (o.tFinal - o.tStart)) o.initFactor, false, true)
    else if rem < ToRat.toRat st.timeStep then (ratUp rem, true, false)
    else if step_withinTolPoly fh st.timeStep o.horizonTol then
      (mulUp st.finitehorizon o.enlarge, false, false)            -- ARCH'23 enlargement
    else (fh, false, false)
  let st₀ : NonlinearSys.LinReachPolyAdaptiveState 𝕋 n :=           -- polyGain at the second step
    if st.i = 2 ∧ o.thirdOrderEmpty ∧ h₀.2.1 = false then
      let orders : Fin n → Option ℕ := fun i => (st.orders i).map (· - 1)
      { st with orders := orders, minorder := step_minorderPoly orders }
    else st
  let L ← fm.step_linReachPolyAdaptiveLoop U o o.fuel
    { st := st₀, timeStep := h₀.1, finitehorizon := h₀.1, errAdm := st.errAdmHorizon, run := 1,
      lastStep := h₀.2.1, veryfirststep := h₀.2.2, timeStepequalHorizon := false,
      zetaP := zero, zetaPh := zero, hor := none }
  let F := if L.1.timeStepequalHorizon then L.1.hor.getD (L.1.timeStep, L.2)  -- Rti_h, Rtp_h
    else (L.1.timeStep, L.2)
  pure { L.1.st with
      i := st.i + 1,
      t := st.t + ToRat.toRat F.1,
      R := F.2.Rtp,
      Rτ := F.2.Rti,
      timeStep := F.1,
      steps := F.1 :: st.steps }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
