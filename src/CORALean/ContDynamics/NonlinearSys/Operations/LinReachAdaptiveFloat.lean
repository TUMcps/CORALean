module

public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAdaptiveOptions
public import CORALean.ContDynamics.NonlinearSys.Operations.AdaptiveOrdersFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachAdaptivePassFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.OptimalDeltatAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.VarphiEstFloat
public import CORALean.Global.Float.RatUp

@[expose] public section

/-!
# CORA's `linReach_adaptive` at `'lin'`, repaired, in floats

One step of `@nonlinearSys/linReach_adaptive.m` at `alg = 'lin'` with CORA's structure and tuning,
[1, Alg. 2] as the code has it: the finite horizon from the last gain (enlarged by `1.1` within
`1e-3` of the last step size), the tensor order of the first step (`aux_initStepTensorOrder`) and
of the next (`aux_nextStepTensorOrder`), and the outer loop: a pass, halved when its error loop
fails; `aux_getPowers` when the zero-width dimensions change; a run at the horizon (decreased by
`decrFactor` at the first step until `varphi` reaches `zetaphi`) giving `aux_optimaldeltat`; a run
at that step size whose gain `aux_varphiest` estimates; the horizon's sets when the two coincide.
Every set returned is a pass's at its own step size; CORA's caches (`gredIdx`, `tt_*`) are omitted.

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

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   11-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- CORA's `withinTol(a, b, tol)`: absolutely or relatively within `tol`. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def step_withinTol (a b tol : 𝕋) : Bool :=
  let d := absolute (subUp a b)
  le d tol || le (divUp d (minimum (absolute a) (absolute b))) tol

/-- `zeroWidthDim`: the dimensions whose generators sum to at most `tol` in magnitude. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def step_zeroWidthDim (R : Zonotope (Vec 𝕋 n)) (tol : 𝕋) : Fin n → Bool :=
  fun i => le (sumUp fun j => absolute (R.G j i)) tol             -- withinTol(sum(abs(G),2),0)

/-- `min(orders)`, the finite ones; `0` if all are `Inf`. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def step_minorder (orders : Fin n → Option ℕ) : ℕ :=
  ((List.finRange n).filterMap orders).foldl min ((List.finRange n).filterMap orders |>.headD 0)

/-- `max(errRatio(~isnan(errRatio)))` over the dimensions in `mask`, `0/0` skipped. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def step_maxRatio (mask : Fin n → Bool) (num den : Vec 𝕋 n) : 𝕋 :=
  maximumOver fun i => if mask i && !(le (num i) zero && le (den i) zero)
    then divUp (num i) (den i) else zero

/-- `aux_initStepTensorOrder`: tensor order `2` from a point, else `2` exactly when the
third-order remainder is above `zetaK` times the second-order one in every nonzero dimension. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_initTensorOrder (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachAdaptiveOptions 𝕋)
    (R : Zonotope (Vec 𝕋 n)) : ℕ :=
  if R.h = 0 then 2 else                                            -- isempty(generators(R))
    let xs := R.c                                                   -- p.x = center(Rstartset)
    let AB := fm.toFloatModel.linearizeFloat xs U.c
    let L2 := (fm.abstrErrAdaptiveFloat 2 AB.1 AB.2 xs R U o.redFactor o.prec).interval.normMag
    let L3 := (fm.abstrErrAdaptiveFloat 3 AB.1 AB.2 xs R U o.redFactor o.prec).interval.normMag
    if ∀ i, le (L2 i) zero = true ∨ le (divUp (L3 i) (L2 i)) o.zetaK = false then 2 else 3

/-- `aux_nextStepTensorOrder`: when the predicted error moved by more than `1 - zetaK`, the other
tensor order's error at the same `Rmax`, and the switch if it wins by `zetaK`. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_nextTensorOrder (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachAdaptiveOptions 𝕋)
    (st : NonlinearSys.LinReachAdaptiveState 𝕋 n) (P : NonlinearSys.LinReachAdaptivePass 𝕋 n)
    (timeStep : 𝕋) : NonlinearSys.LinReachAdaptiveState 𝕋 n :=
  let lim := powUp o.decrFactor (st.minorder + 1)                   -- varphi_lim
  let total := NonlinearSys.varphiTotalFloat o.prec st.varphi lim st.kappaDeltat timeStep
    o.decrFactor                                                    -- varphitotal
  let abstrerr := normUp o.prec P.abstrerr                          -- vecnorm(abstrerr)
  let est := mulUp total abstrerr                                   -- abstrerr_est
  if le (absolute (subUp (divUp est st.kappaAbstrerr) one)) (subUp one o.zetaK) then st
  else
    let κ' := if st.tensorOrder = 2 then 3 else 2                   -- the other tensor order
    let B := (fm.toFloatModel.linearizeFloat P.xs U.c).2
    let V := fm.abstrErrAdaptiveFloat κ' P.A B P.xs P.Rmax U o.redFactor o.prec  -- VerrorDyn
    let Rerror := (LinearSys.canonicalFloat P.A : LinearSys 𝕋 n).errorSolutionAdaptiveFloat
      timeStep o.taylorTerms V none                                 -- errorSolution_adaptive
    let other := normUp o.prec fun i => sumUp fun j => absolute (Rerror.G j i)
    let ratio := if st.tensorOrder = 2 then divUp other abstrerr else divUp abstrerr other
    let switch := if st.tensorOrder = 2 then le ratio o.zetaK else !le ratio o.zetaK
    if switch then
      { st with
          tensorOrder := κ',
          kappaDeltat := timeStep,
          kappaAbstrerr := other,
          errAdmDeltatopt := V.interval.normMag,
          errAdmHorizon := fun _ => zero }
    else st

/-- `options` after a pass: the zero-width dimensions and, when they changed (or at the very
first pass), the orders `q_i` of the abstraction error (`aux_getPowers`). -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_adaptiveOrders (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachAdaptiveOptions 𝕋)
    (L : NonlinearSys.LinReachAdaptiveLoop 𝕋 n) (P : NonlinearSys.LinReachAdaptivePass 𝕋 n) :
    NonlinearSys.LinReachAdaptiveState 𝕋 n :=
  let zw := step_zeroWidthDim L.st.R o.zeroTol
  let orders := NonlinearSys.adaptiveOrdersFloat P.A zw P.Gzero    -- aux_getPowers
    (fm.hess (Interval.point P.xs) (Interval.point U.c)) 100
  if L.veryfirststep ∨ ∃ i, zw i ≠ L.st.zeroWidthDim i              -- rank of Rstart changes
  then { L.st with zeroWidthDim := zw, orders := orders, minorder := step_minorder orders }
  else L.st

/-- `zetaP`: `exp(trace(A*timeStep))` at the first run, else as it was. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def step_adaptiveZetaP (o : NonlinearSys.LinReachAdaptiveOptions 𝕋)
    (L : NonlinearSys.LinReachAdaptiveLoop 𝕋 n) (P : NonlinearSys.LinReachAdaptivePass 𝕋 n) : 𝕋 :=
  if L.run = 1 then expUp o.prec (sumUp fun i => mulUp (P.A i i) L.timeStep) else L.zetaP

/-- The first run (at the horizon) after a pass: the locals the loop continues with, `run` set
to `0` where CORA's `continue` skips the run counter. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_adaptiveHorizon (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachAdaptiveOptions 𝕋)
    (L : NonlinearSys.LinReachAdaptiveLoop 𝕋 n) (P : NonlinearSys.LinReachAdaptivePass 𝕋 n) :
    NonlinearSys.LinReachAdaptiveLoop 𝕋 n :=
  let decr := o.decrFactor
  let zetaP := step_adaptiveZetaP o L P
  let st := fm.step_adaptiveOrders U o L P
  let mask := fun i => decide (st.orders i = some st.minorder)      -- orders == minorder
  let zetaphi := o.zetaphi ⟨min st.minorder 2, by omega⟩             -- zetaphi(minorder+1)
  let hor := (L.hor.map (·.2)).getD P                               -- Rerror_h
  let rR := normUp o.prec fun i => sumUp fun j => absolute (st.R.G j i)
  let decrErr := fun i => mulUp decr (P.trueError i)                -- decrFactor * trueError
  if st.i = 1 then
    if L.veryfirststep then                                         -- save, decrease, again
      { L with
        st := st, veryfirststep := false, zetaP := zetaP, zetaPh := zetaP,
        hor := some (L.timeStep, P), timeStep := mulUp decr L.timeStep, errAdm := decrErr,
        run := 0 }
    else
      let varphi := step_maxRatio mask P.abstrerr hor.abstrerr      -- max(errRatio)
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
            (normUp o.prec hor.abstrerr) L.finitehorizon varphi L.zetaPh,  -- aux_optimaldeltat
          errAdm := fun _ => zero }
  else
    let Δt := NonlinearSys.optimalDeltatAdaptiveFloat o.prec decr o.redFactor rR
      (normUp o.prec P.abstrerr) L.finitehorizon st.varphi zetaP    -- aux_optimaldeltat
    { L with
      st := { st with errAdmHorizon := P.trueError },
      zetaP := zetaP, hor := some (L.timeStep, P), errAdm := st.errAdmDeltatopt,
      timeStep := if ToRat.toRat Δt ≤ o.tFinal - st.t then Δt else ratUp (o.tFinal - st.t) }

/-- The second run (at the tuned step size), or the last step's only one: the locals the loop
ends on, with the gain, the errors and the tensor order of the next step. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_adaptiveFinish (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachAdaptiveOptions 𝕋)
    (L : NonlinearSys.LinReachAdaptiveLoop 𝕋 n) (P : NonlinearSys.LinReachAdaptivePass 𝕋 n) :
    NonlinearSys.LinReachAdaptiveLoop 𝕋 n :=
  let st := fm.step_adaptiveOrders U o L P
  let mask := fun i => decide (st.orders i = some st.minorder)      -- orders == minorder
  let hor := (L.hor.map (·.2)).getD P                               -- Rerror_h
  let varphi := if L.timeStepequalHorizon then step_maxRatio mask P.abstrerr hor.abstrerr
    else if L.lastStep = false then
      NonlinearSys.varphiEstFloat o.prec L.finitehorizon L.timeStep hor.abstrerr P.abstrerr
        o.decrFactor mask st.minorder o.varphiTol o.varphiStep o.fuel  -- aux_varphiest
    else st.varphi
  let st : NonlinearSys.LinReachAdaptiveState 𝕋 n := { st with
    varphi := varphi, finitehorizon := L.finitehorizon, errAdmDeltatopt := P.trueError }
  let st : NonlinearSys.LinReachAdaptiveState 𝕋 n := if st.i = 1 then  -- kappa_deltat, ..
      { st with kappaDeltat := L.timeStep, kappaAbstrerr := normUp o.prec P.abstrerr }
    else if L.lastStep = false then fm.step_nextTensorOrder U o st P L.timeStep
    else st
  { L with st := st, zetaP := step_adaptiveZetaP o L P }

/-- What the outer loop does after a pass `P` at `L.timeStep`: `inl` the locals it continues
with (the run counter advanced, and the horizon test), `inr` the locals it ends on. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_linReachAdaptiveDecide (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachAdaptiveOptions 𝕋)
    (L : NonlinearSys.LinReachAdaptiveLoop 𝕋 n) (P : NonlinearSys.LinReachAdaptivePass 𝕋 n) :
    NonlinearSys.LinReachAdaptiveLoop 𝕋 n ⊕ NonlinearSys.LinReachAdaptiveLoop 𝕋 n :=
  if L.run = 1 ∧ L.lastStep = false then
    let L₁ := fm.step_adaptiveHorizon U o L P                       -- run using finite horizon
    if L₁.run = 0 then .inl { L₁ with run := 1 }                    -- continue
    else if le L₁.timeStep L₁.finitehorizon && le L₁.finitehorizon L₁.timeStep then
      .inl { L₁ with                                                -- timeStepequalHorizon
        run := L₁.run + 1, timeStepequalHorizon := true,
        timeStep := mulUp L₁.timeStep o.decrFactor }
    else .inl { L₁ with run := L₁.run + 1 }
  else .inr (fm.step_adaptiveFinish U o L P)                        -- second run: break

/-- The outer `while true` loop of the step: a pass at the current step size, halved when it
fails, and what `step_linReachAdaptiveDecide` makes of it; the locals and the pass it ends on, or
none once `fuel` runs out. -/
@[step_of NonlinearSys.FloatHessModel.linReachAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_linReachAdaptiveLoop (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachAdaptiveOptions 𝕋) :
    ℕ → NonlinearSys.LinReachAdaptiveLoop 𝕋 n →
      Option (NonlinearSys.LinReachAdaptiveLoop 𝕋 n × NonlinearSys.LinReachAdaptivePass 𝕋 n)
  | 0, _ => none
  | fuel + 1, L =>
    match fm.linReachAdaptivePassFloat L.st.tensorOrder U ⟨⟨L.timeStep, o.taylorTerms⟩,
      o.zonotopeOrder⟩ o.enlarge o.redFactor o.prec o.fuel L.st.R L.errAdm o.linearStep with
    | none =>                                                       -- ~Lconverged: halve
      fm.step_linReachAdaptiveLoop U o fuel { L with
        timeStep := half L.timeStep, finitehorizon := half L.timeStep,
        errAdm := L.st.errAdmHorizon }
    | some P =>
      match fm.step_linReachAdaptiveDecide U o L P with
      | .inl L₁ => fm.step_linReachAdaptiveLoop U o fuel L₁        -- continue
      | .inr L₂ => some (L₂, P)                                     -- break


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One step of CORA's `linReach_adaptive` from `st`: the state after it, its sets unreduced,
or none if its loop runs out of `fuel`. -/
def NonlinearSys.FloatHessModel.linReachAdaptiveFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachAdaptiveOptions 𝕋)
    (st : NonlinearSys.LinReachAdaptiveState 𝕋 n) :
    Option (NonlinearSys.LinReachAdaptiveState 𝕋 n) := do
  let rem := o.tFinal - st.t                                        -- tFinal - options.t
  let zetaphi := o.zetaphi ⟨min st.minorder 2, by omega⟩
  let fh := mulUp st.finitehorizon (subUp (addUp one st.varphi) zetaphi)  -- finitehorizon
  let h₀ : 𝕋 × Bool × Bool :=                                       -- timeStep, last, first
    if st.i = 1 then (mulUp (ratUp (o.tFinal - o.tStart)) o.initFactor, false, true)
    else if rem < ToRat.toRat st.timeStep then (ratUp rem, true, false)
    else if step_withinTol fh st.timeStep o.horizonTol then
      (mulUp st.finitehorizon o.enlarge, false, false)            -- ARCH'23 enlargement
    else (fh, false, false)
  let st₀ : NonlinearSys.LinReachAdaptiveState 𝕋 n :=                -- aux_initStepTensorOrder
    if st.i = 1 then { st with tensorOrder := fm.step_initTensorOrder U o st.R } else st
  let L ← fm.step_linReachAdaptiveLoop U o o.fuel
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
