module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.HessRemainder
public import CORALean.ContDynamics.NonlinearSys.Operations.LinPointFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.LinearizeFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.OneStepFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# One step of CORA's `linReach` at `alg = 'lin'`, with its error loop, in floats

`linReach.m` bounds the abstraction error by a loop: apply `1.1 abstrerr` (the last step's error)
as an input box, run the linearized system with it (`Rmax`), read the Lagrange remainder over
`Rmax` (`priv_abstrerr_lin`) and accept once its magnitude `trueError` is within the box, else go
round with `abstrerr = trueError`. The sets are one linear step with input
`f(z✱) ⊕ B(U - u✱) ⊕ VerrorDyn`. The step fails if `trueError` exceeds `maxError` (CORA splits)
or `fuel` runs out. As in the adaptive pass, the Hessian is read over `Rmax` joined with `p`, and
`Rmax` is one `oneStepFloat` with the error in its input. The guess is tested as
`trueError ≤ e`, which a rounded quotient `trueError ./ e ≤ 1` can pass by an ulp.

## Inputs
* `fm` – float Hessian model
* `U` – input zonotope
* `options` – reachability options
* `enlarge` – enlargement of the error, CORA's `1.1`
* `fuel` – iteration bound
* `R` – start zonotope
* `abstrerr` – the last step's abstraction error
* `maxError` – largest admissible error, if any
* `step` – linear step

## Output
* the time-interval and end sets of the step and its abstraction error, or none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The loop: `(Rmax, VerrorDyn, trueError)` of the first pass whose `trueError` is at most its
applied error `1.1 abstrerr`, the next pass applying `1.1 trueError`; none if a linear step fails,
`perfInd` exceeds `1`, or `fuel` runs out. -/
@[step_of NonlinearSys.FloatHessModel.linReachLoopFloat]
def NonlinearSys.FloatHessModel.step_abstrErrLoopLin (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (Vbase R : Zonotope (Vec 𝕋 n))
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachFloatOptions 𝕋) (enlarge : 𝕋)
    (maxError : Option (Vec 𝕋 n)) (step : NonlinearSys.LinearStep) :
    ℕ → Vec 𝕋 n → Option (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Vec 𝕋 n)
  | 0, _ => none
  | fuel + 1, abstrerr =>
    let appliedError := fun i => mulUp enlarge (abstrerr i)         -- 1.1*abstrerr
    let Verror := (⟨-appliedError, appliedError⟩ : Interval (Vec 𝕋 n)).zonotope  -- zonotope(0,diag)
    match NonlinearSys.oneStepFloat A xs (Vbase ⊞ Verror) R options  -- Rmax = Rti+RallError
        step with
    | none => none
    | some (Rmax, _) =>
      let Ω := Rmax.interval                                        -- interval(Rmax) + p.x
      let X : Interval (Vec 𝕋 n) :=                                 -- Ω, holding p.x too
        ⟨fun i => minimum (Ω.inf i) (xs i), fun i => maximum (Ω.sup i) (xs i)⟩
      let Ub := U.interval                                          -- interval(params.U)
      let U' : Interval (Vec 𝕋 m) :=                                -- U's box, holding p.u too
        ⟨fun i => minimum (Ub.inf i) (U.c i), fun i => maximum (Ub.sup i) (U.c i)⟩
      let VerrorDyn := (fm.hessRemainder A B xs U.c X U').zonotope  -- priv_abstrerr_lin
      let trueError := VerrorDyn.interval.normMag                   -- abs(c) + sum(abs(G))
      if (maxError.map fun mx => decide (∃ i, le (trueError i) (mx i) = false)).getD false
      then none                                                     -- perfInd > 1: CORA splits
      else if ∀ i, le (trueError i) (appliedError i) = true then some (Rmax, VerrorDyn, trueError)
      else fm.step_abstrErrLoopLin A B xs Vbase R U options enlarge maxError step fuel trueError


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(R(τ_k), R(t_{k+1}), abstrerr)` from `R = R(t_k)` under inputs in `U`, the abstraction error
bounded by CORA's loop from the last step's `abstrerr`, or `none` if the loop or the linear step
fails. -/
def NonlinearSys.FloatHessModel.linReachLoopFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachFloatOptions 𝕋) (enlarge : 𝕋) (fuel : ℕ)
    (R : Zonotope (Vec 𝕋 n)) (abstrerr : Vec 𝕋 n) (maxError : Option (Vec 𝕋 n) := none)
    (step : NonlinearSys.LinearStep := .reachFloatInput) :
    Option (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Vec 𝕋 n) := do
  let Δt := options.Δt                                              -- options.timeStep
  let xs := (fm.linPointFloat Δt R U).1                             -- p.x
  let us := U.c                                                     -- p.u
  let A := (fm.linearizeFloat xs us).1                              -- A
  let B := (fm.linearizeFloat xs us).2                              -- B
  let f₀ := fm.f (Interval.point xs) (Interval.point us)            -- f0
  let Vbase := f₀.zonotope ⊞                                        -- uTrans ⊕ B(U - p.u)
    Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B (Recenter.recenter U)
  let E ← fm.step_abstrErrLoopLin A B xs Vbase R U options enlarge maxError step fuel abstrerr
  let S ← NonlinearSys.oneStepFloat A xs (Vbase ⊞ E.2.1) R options step  -- Rti, Rtp with VerrorDyn
  pure (S.1, S.2, E.2.2)                                            -- Rtp.error = trueError

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
