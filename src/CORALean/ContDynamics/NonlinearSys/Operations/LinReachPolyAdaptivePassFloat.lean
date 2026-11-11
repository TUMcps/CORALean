module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachFloatOptions
public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat
public import CORALean.ContDynamics.LinearSys.Operations.ErrorSolutionAdaptiveFloat
public import CORALean.ContDynamics.LinearSys.Operations.PolyPointFloat
public import CORALean.ContDynamics.LinearSys.Operations.PolyWindowFloat
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachPolyAdaptiveLoop
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolyAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.PrecompStatErrorAdaptiveFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.HessRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPointFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinearizeFloat
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.CartProd
public import CORALean.ContSet.PolyZonotope.Float.Operations.Materialise
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapMixed
public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceAdaptive
public import CORALean.ContSet.Zonotope.Float.Operations.CartProd
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceAdaptive

@[expose] public section

/-!
# One pass of CORA's `linReach_adaptive` at `'poly'` and a fixed `Δt`, repaired, in floats

The body of the outer loop at `alg = 'poly'` up to `Rerror`: `linearize`, the static error
`½ quadMap(Z, H)` over the reduced start set (`priv_precompStatError_adaptive`), kept as a
polynomial, and the loop until `trueError ≤ error_adm`, the box of `VerrorDyn` and the static
error together. `Rdiff` is the window's differences with input `f0 ⊕ B(U - p.u) ⊕ [-error_adm,
error_adm]`; the end set adds the static error's dependent part by `exactPlus`. Repairs: the region
joins the box with `p.x`, `RallError` and `VerrorDyn` enter the window over the whole step, the
time-interval set includes the static error, and the step is none unless `options.Δt > 0`.

## Inputs
* `fm` – float Hessian model
* `U` – input zonotope
* `options` – reachability options
* `enlarge` – enlargement of the admissible error
* `redFactor` – reduction factor
* `p` – square root precision
* `fuel` – iteration bound
* `R` – start polynomial zonotope
* `errorAdm` – initial admissible error

## Output
* the sets of the pass and what the tuning reads, or none
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

/-- The inner loop: `(VerrorDyn, trueError)` of the first pass whose `trueError` is at most its
`error_adm`, or none once it gives up or `fuel` runs out. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyAdaptivePassFloat]
def NonlinearSys.FloatHessModel.step_abstrErrLoopPolyAdaptive
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n)
    (Vbase : Zonotope (Vec 𝕋 n)) (Rdelta Vstat : PolyZonotope (Vec 𝕋 n))
    (Zdelta : Zonotope (Vec 𝕋 (n + m))) (U : Zonotope (Vec 𝕋 m))
    (options : LinearSys.ReachFloatOptions 𝕋) (enlarge redFactor : 𝕋) (p : ℕ) :
    ℕ → ℕ → 𝕋 → Vec 𝕋 n → Option (Zonotope (Vec 𝕋 n) × Vec 𝕋 n)
  | 0, _, _, _ => none
  | fuel + 1, perfIndCounter, perfIndPrev, errorAdm =>
    let Verror := (⟨-errorAdm, errorAdm⟩ : Interval (Vec 𝕋 n)).zonotope  -- zonotope(0,diag(..))
    let pt := fun v =>
      (⟨0, v, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope (Vec 𝕋 n))
    let Vsz := Vstat.zonotopeEven.materialise                       -- zonotope(Vstat)
    -- Rdiff: the differences over the step, with RallError (total error within error_adm) as input
    (LinearSys.canonicalFloat A : LinearSys 𝕋 n).polyWindowFloat options.Δt options.η
        (Vbase ⊞ Verror) Rdelta |>.bind fun W =>
      let Rdiff := W.2
      let Rmax := ((Rdelta.zonotopeEven.materialise ⊞ Rdiff.zonotopeEven.materialise) ⊞
        pt xs).materialise                                          -- Rdelta+zonotope(Rdiff), abs.
      let VerrorDyn := fm.abstrErrPolyAdaptiveFloat A B xs Rmax Zdelta Rdiff U redFactor p
      let trueError := (VerrorDyn ⊞ Vsz).interval.normMag           -- abs(c) + sum(abs(G))
      let perfIndCurr := maximumOver fun i =>                       -- max(trueError./
        if le (trueError i) zero then zero else divUp (trueError i) (errorAdm i)  -- error_adm)
      if ∀ i, le (trueError i) (errorAdm i) = true then some (VerrorDyn, trueError)
      else if 2 < perfIndCounter ∧ le perfIndCurr perfIndPrev = false then none  -- diverging
      else fm.step_abstrErrLoopPolyAdaptive A B xs Vbase Rdelta Vstat Zdelta U options enlarge
        redFactor p fuel (perfIndCounter + 1) perfIndCurr fun i => mulUp enlarge (trueError i)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One linearization at `options.Δt` from `R`: the inner loop from `errorAdm`, then the step's
sets with the error it accepted, or none if `options.Δt` is not positive or the loop or a linear
step fails. -/
def NonlinearSys.FloatHessModel.linReachPolyAdaptivePassFloat
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (U : Zonotope (Vec 𝕋 m))
    (options : LinearSys.ReachFloatOptions 𝕋) (enlarge redFactor : 𝕋) (p fuel : ℕ)
    (R : PolyZonotope (Vec 𝕋 n)) (errorAdm : Vec 𝕋 n) :
    Option (NonlinearSys.LinReachPolyAdaptivePass 𝕋 n) := do
  let Δt := options.Δt                                              -- options.timeStep
  let _ ← if ltStrict zero Δt = true then some () else none         -- a step of positive width
  let Rc : Zonotope (Vec 𝕋 n) := ⟨0, R.c, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩
  let xs := (fm.toFloatModel.linPointFloat Δt Rc U).1               -- p.x
  let us := U.c                                                     -- p.u
  let A := (fm.toFloatModel.linearizeFloat xs us).1                 -- A
  let B := (fm.toFloatModel.linearizeFloat xs us).2                 -- B
  let f₀ := fm.f (Interval.point xs) (Interval.point us)            -- f0
  let Vbase := f₀.zonotope ⊞                                        -- uTrans ⊕ B(U - p.u)
    Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U)
  let lin : LinearSys 𝕋 n := LinearSys.canonicalFloat A
  let Rdelta := R ⊞ (Interval.point (-xs)).zonotope.ofIndep         -- Rstart + (-p.x)
  let S := fm.precompStatErrorAdaptiveFloat xs U redFactor p Rdelta  -- errorStat, Zdelta
  let E ← fm.step_abstrErrLoopPolyAdaptive A B xs Vbase Rdelta S.1 S.2 U options enlarge
    redFactor p fuel 1 zero errorAdm                                -- the loop
  let Vdyn := E.1                                                   -- VerrorDyn
  let Vsz := S.1.zonotopeEven.materialise                           -- zonotope(Vstat)
  let W ← lin.polyWindowFloat Δt options.η ((Vbase ⊞ Vdyn) ⊞ Vsz) Rdelta  -- Rti
  let Rtp ← lin.polyPointFloat Δt options.η (Vbase ⊞ Vdyn) Rdelta S.1  -- Rtp, exactPlus
  let pt := (Interval.point xs).zonotope.ofIndep                    -- + p.x
  let Rerror := (lin.errorSolutionAdaptiveFloat Δt options.η Vdyn none).ofIndep ⊞   -- Rerror
    PolyZonotope.mtimesIntervalMat (MatExp.adaptiveIntegral (Interval.point A) Δt options.η) S.1
  pure { Rti := W.1 ⊞ pt, Rtp := Rtp ⊞ pt, A := A, xs := xs, trueError := E.2,
         abstrerr := fun i => sumUp fun j => absolute (Rerror.GI j i),  -- sum(abs(Rerror.GI),2)
         Gzero := fun i => le (sumUp fun j => absolute (Vdyn.G j i)) zero }  -- vecnorm(G,1,2)==0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
