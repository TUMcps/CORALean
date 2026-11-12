module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPolyAdaptiveFloat
public import CORALean.ContSet.PolyZonotope.Float.Operations.GirardSplit
public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceBy
public import CORALean.ContSet.PolyZonotope.Float.Operations.Restructure

@[expose] public section

/-!
# CORA's `reach_adaptive` at `'poly'`, in floats

`@nonlinearSys/reach_adaptive.m` at `alg = 'poly-adaptive'`: the steps of `linReach_adaptive` until
the end time, each from the set at the end of the step before. A set whose independent generators'
volume exceeds `maxPolyZonoRatio` of the dependent part's (`approxVolumeRatio`, the interval
method) is restructured before the step; the time-point set is reduced adaptively at `redFactor`
and then to `maxDepGenOrder` dependent generators (`aux_reduceOnlyDep`), the time-interval set
at `5 redFactor`. CORA restructures by `reducePca`; `PolyZonotope.restructure` stands in for it
here, which is sound and can be wider (CORA does it at 5 of 1193 steps of LALO20 W = 0.1).

## Inputs
* `fm` – float Hessian model
* `U` – input zonotope
* `o` – adaptive options
* `maxPolyZonoRatio` – the volume ratio above which a set is restructured

## Output
* the states after each step, or none if a step fails
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

/-- `aux_checkForAbortion`: the remaining time over the sum of the last ten step sizes exceeds
`abortRatio`. -/
@[step_of NonlinearSys.FloatHessModel.reachPolyAdaptiveFloat]
def step_abortPolyAdaptive (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋) (t : ℚ)
    (steps : List 𝕋) : Bool :=
  let lastNsteps := ((steps.take 10).map ToRat.toRat).sum           -- sum(tVec(end-N+1:end))
  steps ≠ [] && decide (ToRat.toRat o.abortRatio * lastNsteps < o.tFinal - t)

/-- `approxVolumeRatio(R, 'interval') > maxPolyZonoRatio`: the independent part's box against the
dependent part's over the dimensions where both have width, `Vind > ratio^n Vdep`. -/
@[step_of NonlinearSys.FloatHessModel.reachPolyAdaptiveFloat]
def step_volumeRatioExceeds (R : PolyZonotope (Vec 𝕋 n)) (ratio : 𝕋) : Bool :=
  if R.q = 0 then false                                             -- isempty(GI): ratio = 0
  else if R.h = 0 then true                                         -- isempty(G): ratio = Inf
  else
    let radInd : Vec 𝕋 n := fun i => sumUp fun j => absolute (R.GI j i)  -- rad(interval(Z))
    let Idep := ({ R with q := 0, GI := Fin.elim0 } : PolyZonotope (Vec 𝕋 n)).zonotopeEven.interval
    let radDep : Vec 𝕋 n := fun i => half (subUp (Idep.sup i) (Idep.inf i))  -- rad(Idep)
    let ind := (List.finRange n).filter fun i =>
      !(le (radDep i) zero) && !(le (radInd i) zero)               -- rad ~= 0 in both
    let vol := fun (r : Vec 𝕋 n) => ind.foldl (fun acc i => mulUp acc (addUp (r i) (r i))) one
    !(le (vol radInd) (mulUp (powUp ratio n) (vol radDep)))         -- (Vind/Vdep)^(1/n) > ratio

/-- `aux_reduceOnlyDep`: past `order` times `n` dependent generators, the shortest boxed, then
equal exponent columns added. -/
@[step_of NonlinearSys.FloatHessModel.reachPolyAdaptiveFloat]
def step_reduceOnlyDep (R : PolyZonotope (Vec 𝕋 n)) (order p : ℕ) : PolyZonotope (Vec 𝕋 n) :=
  if R.h < (order + 1) * n then R                                   -- Gsize/n < order+1
  else (R.reduceBy (PolyZonotope.girardSplit (fun l => normUp p (R.G l)) (order * n))
    ((Partition.split R.q 0).reindex (finCongr (Nat.add_zero R.q).symm))).compactGens


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The states after at most `k` steps of CORA's `reach_adaptive` at `'poly'` from `s`, each with
its sets reduced, or none if a step fails. -/
def NonlinearSys.FloatHessModel.reachPolyAdaptiveFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋)
    (maxPolyZonoRatio : 𝕋) :
    ℕ → NonlinearSys.LinReachPolyAdaptiveState 𝕋 n →
      Option (List (NonlinearSys.LinReachPolyAdaptiveState 𝕋 n))
  | 0, _ => some []
  | k + 1, s =>
    if ToRat.toRat o.endTol < o.tFinal - s.t ∧ step_abortPolyAdaptive o s.t s.steps = false
    then do                                                         -- MAIN LOOP
      let s₀ := if step_volumeRatioExceeds s.R maxPolyZonoRatio     -- restructure R
        then { s with R := s.R.restructure } else s
      let s' ← fm.linReachPolyAdaptiveFloat U o s₀                  -- linReach_adaptive
      let s'' := { s' with                                          -- reduction for next step
        R := step_reduceOnlyDep (s'.R.reduceAdaptive o.redFactor o.prec) o.maxDepGenOrder o.prec,
        Rτ := s'.Rτ.reduceAdaptive (mulUp o.redFactor (nsmulUp 5 one)) o.prec }
      let rest ← fm.reachPolyAdaptiveFloat U o maxPolyZonoRatio k s''
      pure (s'' :: rest)
    else some []

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
