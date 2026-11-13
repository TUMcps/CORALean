module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachFloatOptions
public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat
public import CORALean.ContDynamics.LinearSys.Operations.PolyOneStepClosedFormFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.HessRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPointFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinearizeFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ZonotopeFold
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# One step of CORA's `linReach` at `alg = 'lin'` from a polynomial zonotope, in floats

`linReachLoopFloat` with the start set a polynomial zonotope: `[e^{AΔt}] R` keeps the dependency
on the factors, and the error loop of `linReach.m` is the zonotope loop's. The guess `1.1 abstrerr`
enters the input of one pass of `step_polyOneStepFloat`, `zonotope(Rmax)` (the even generators
halved into the center, `PolyZonotope.zonotopeFold`) is the set the Hessian is read over, joined
with `p.x`, and the pass is accepted once `trueError ≤ 1.1 abstrerr`, else the next guess is
`trueError`. The step fails if `trueError` exceeds `maxError` (CORA splits) or `fuel` runs out.
The point `p.x` is the zonotope step's, taken at the center of `R`. The sets are one pass with
`f(z✱) ⊕ B(U - u✱) ⊕ VerrorDyn` as input, the error entering as independent generators.

## Inputs
* `fm` – float Hessian model
* `U` – input zonotope
* `options` – reachability options
* `enlarge` – enlargement of the error, CORA's `1.1`
* `fuel` – iteration bound
* `R` – start polynomial zonotope
* `abstrerr` – the last step's abstraction error
* `maxError` – largest admissible error, if any
* `order` – the order of equal exponent columns (CORA's hash order)

## Output
* the time-interval and end sets of the step and its abstraction error, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `(R(τ_k), R(t_{k+1}))` of `δ̇ = A δ + ũ`, `ũ ∈ V`, from `R - x✱`, shifted back by `x✱`; `none`
if the step is not positive or the linear step fails. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyLoopFloat]
def NonlinearSys.step_polyOneStepFloat (A : Mat 𝕋 n n) (xs : Vec 𝕋 n)
    (V : Zonotope (Vec 𝕋 n)) (R : PolyZonotope (Vec 𝕋 n)) (options : LinearSys.ReachFloatOptions 𝕋)
    (order : ℕ → Array (Array ℕ) → Array ℕ) (M : LinearSys.ClosedFormMatrices 𝕋 n) :
    Option (PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n)) :=
  let pt := fun v => (⟨0, v, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ :
    Zonotope (Vec 𝕋 n)).ofIndep
  if ltStrict zero options.Δt then
    let S := (LinearSys.canonicalFloat A : LinearSys 𝕋 n).polyOneStepClosedFormFloat M  -- one step
      (R ⊞ pt (-xs)) (Recenter.recenter V) V.c options.Δt order      -- from R - x✱
    some (S.Rti ⊞ pt xs, S.Rtp ⊞ pt xs)                             -- Rti + p.x, Rtp + p.x
  else none

/-- The loop: `(Rmax, VerrorDyn, trueError)` of the first pass with `trueError` at most its applied
error `1.1 abstrerr`, the next pass applying `1.1 trueError`; none if a pass fails, `perfInd`
exceeds `1`, or `fuel` runs out. `Rmax` is the zonotope of the pass's time-interval set. -/
@[step_of NonlinearSys.FloatHessModel.linReachPolyLoopFloat]
def NonlinearSys.FloatHessModel.step_abstrErrLoopLinPoly (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (Vbase : Zonotope (Vec 𝕋 n))
    (R : PolyZonotope (Vec 𝕋 n)) (U : Zonotope (Vec 𝕋 m))
    (options : LinearSys.ReachFloatOptions 𝕋) (enlarge : 𝕋) (maxError : Option (Vec 𝕋 n))
    (order : ℕ → Array (Array ℕ) → Array ℕ) (M : LinearSys.ClosedFormMatrices 𝕋 n) :
    ℕ → Vec 𝕋 n → Option (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Vec 𝕋 n)
  | 0, _ => none
  | fuel + 1, abstrerr =>
    let appliedError := fun i => mulUp enlarge (abstrerr i)         -- 1.1*abstrerr
    let Verror := (⟨-appliedError, appliedError⟩ : Interval (Vec 𝕋 n)).zonotope  -- zonotope(0,diag)
    -- Rti + RallError
    match NonlinearSys.step_polyOneStepFloat A xs (Vbase ⊞ Verror) R options order M
    with
    | none => none
    | some (Rmax, _) =>
      let Z := Rmax.zonotopeFold.materialise                        -- zonotope(Rmax), abs.
      let Ω := Z.interval                                           -- interval(Z) + p.x
      let X : Interval (Vec 𝕋 n) :=                                 -- Ω, holding p.x too
        ⟨fun i => minimum (Ω.inf i) (xs i), fun i => maximum (Ω.sup i) (xs i)⟩
      let Ub := U.interval                                          -- interval(params.U)
      let U' : Interval (Vec 𝕋 m) :=                                -- U's box, holding p.u too
        ⟨fun i => minimum (Ub.inf i) (U.c i), fun i => maximum (Ub.sup i) (U.c i)⟩
      let VerrorDyn := (fm.hessRemainder A B xs U.c X U').zonotope  -- priv_abstrerr_lin
      let trueError := VerrorDyn.interval.normMag                   -- abs(c) + sum(abs(G))
      if (maxError.map fun mx => decide (∃ i, le (trueError i) (mx i) = false)).getD false
      then none                                                     -- perfInd > 1: CORA splits
      else if ∀ i, le (trueError i) (appliedError i) = true then some (Z, VerrorDyn, trueError)
      else fm.step_abstrErrLoopLinPoly A B xs Vbase R U options enlarge maxError order M fuel
        trueError


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(R(τ_k), R(t_{k+1}), abstrerr)` from `R = R(t_k)` under inputs in `U`, the abstraction error
bounded by CORA's loop from the last step's `abstrerr`, or `none` if the loop or the step fails. -/
def NonlinearSys.FloatHessModel.linReachPolyLoopFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachFloatOptions 𝕋) (enlarge : 𝕋) (fuel : ℕ)
    (R : PolyZonotope (Vec 𝕋 n)) (abstrerr : Vec 𝕋 n) (maxError : Option (Vec 𝕋 n) := none)
    (order : ℕ → Array (Array ℕ) → Array ℕ) :
    Option (PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n) × Vec 𝕋 n) := do
  let Δt := options.Δt                                              -- options.timeStep
  let Rc : Zonotope (Vec 𝕋 n) := ⟨0, R.c, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩
  let xs := (fm.linPointFloat Δt Rc U).1                            -- p.x, at the center of R
  let us := U.c                                                     -- p.u
  let A := (fm.linearizeFloat xs us).1                              -- A
  let B := (fm.linearizeFloat xs us).2                              -- B
  let f₀ := fm.f (Interval.point xs) (Interval.point us)            -- f0
  let Vbase := f₀.zonotope ⊞                                        -- uTrans ⊕ B(U - p.u)
    Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U)
  let M ← (LinearSys.canonicalFloat A : LinearSys 𝕋 n).closedFormMatricesFloat Δt  -- once per
    (max 2 options.η)                                               -- linearization, not per pass
  let E ← fm.step_abstrErrLoopLinPoly A B xs Vbase R U options enlarge maxError order M fuel
    abstrerr
  -- Rti, Rtp
  let S ← NonlinearSys.step_polyOneStepFloat A xs (Vbase ⊞ E.2.1) R options order M
  pure (S.1, S.2, E.2.2)                                            -- Rtp.error = trueError

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
