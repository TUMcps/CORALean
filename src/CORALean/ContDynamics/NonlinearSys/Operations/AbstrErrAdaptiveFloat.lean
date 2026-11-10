module

public import CORALean.ContDynamics.NonlinearSys.Operations.HessRemainder
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.CenterMat
public import CORALean.ContSet.Zonotope.Float.Operations.CartProd
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMap
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceAdaptive
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `priv_abstractionError_adaptive` at `'lin'`, repaired, in floats

CORA's `VerrorDyn` for `Rmax` (in absolute coordinates) and `U`, read over the box of `Rmax`
*joined with the linearization point*: CORA's `interval(R) + p.x` misses the segment the Lagrange
form needs (`linReachAdaptiveCora1D_hessianRegion_counterexample`). Tensor order `2` is
`hessRemainder` there (`0.5 * dz' * H_ * dz`). Tensor order `3` is CORA's `errorSec = 0.5 *
quadMap(Z, H)`, `Z = cartProd(reduce(R,'adaptive',sqrt(redFactor)), U)`, `H` the midpoint of the
Hessian box at `p`, plus `½ dzᵀ |H(X) - H| dz` in place of CORA's misindexed third-order term
(`abstrErrAdaptiveTensor3Cora2D_counterexample`); both are zero for a quadratic field. The sum is
reduced by `reduce(…,'adaptive',10*redFactor)`.

## Inputs
* `fm` – float Hessian model
* `κ` – tensor order
* `A` – state matrix
* `B` – input matrix
* `xs` – state expansion point
* `Rmax` – state set
* `U` – input zonotope
* `redFactor` – reduction factor
* `p` – square root precision

## Output
* the abstraction error zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The model with its Hessian boxes shifted by `-Hp`: `hessRemainder` of it bounds what the
Hessian over a box differs from `Hp` by. -/
@[step_of NonlinearSys.FloatHessModel.abstrErrAdaptiveFloat]
def NonlinearSys.FloatHessModel.step_hessShift (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (Hp : Fin n → Mat 𝕋 (n + m) (n + m)) : NonlinearSys.FloatHessModel 𝕋 n m :=
  { fm with hess := fun X U i => Interval.matPlus (fm.hess X U i) (Interval.point (-Hp i)) }

/-- The box of `I` joined with the point `v`. -/
@[step_of NonlinearSys.FloatHessModel.abstrErrAdaptiveFloat]
def step_hullPoint {k : ℕ} (I : Interval (Vec 𝕋 k)) (v : Vec 𝕋 k) : Interval (Vec 𝕋 k) :=
  ⟨fun i => minimum (I.inf i) (v i), fun i => maximum (I.sup i) (v i)⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `VerrorDyn` at `'lin'` and tensor order `κ` for `Rmax` (absolute) and `U`, its
Hessian read over the box of `Rmax` joined with the linearization point. -/
def NonlinearSys.FloatHessModel.abstrErrAdaptiveFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (κ : ℕ) (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (Rmax : Zonotope (Vec 𝕋 n))
    (U : Zonotope (Vec 𝕋 m)) (redFactor : 𝕋) (p : ℕ) : Zonotope (Vec 𝕋 n) :=
  let us := U.c                                                     -- p.u
  let X := step_hullPoint Rmax.interval xs                               -- totalInt_x, holding p.x
  let U' := step_hullPoint U.interval us                                 -- totalInt_u, holding p.u
  if κ = 3 then
    let pt : Zonotope (Vec 𝕋 n) := ⟨0, -xs, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩
    let Rred := (Rmax ⊞ pt).reduceAdaptive (sqrtUp p redFactor) p   -- reduce(R,'adaptive',..)
    let Z := Rred.cartProd (Recenter.recenter U)                    -- Z = cartProd(Rred,U)
    let Hp := fun i => (fm.hess (Interval.point xs) (Interval.point us) i).centerMat  -- H at p
    let errorSec := Z.quadMap fun i a b => half (Hp i a b)          -- 0.5*quadMap(Z,H)
    let rest := (fm.step_hessShift Hp).hessRemainder A B xs us X U'      -- |H(X) - H| and A, B
    (errorSec ⊞ rest.zonotope).reduceAdaptive                       -- reduce(VerrorDyn,
      (mulUp (nsmulUp 10 one) redFactor) p                          --   'adaptive',10*rf)
  else (fm.hessRemainder A B xs us X U').zonotope                   -- 0.5 * dz' * H_ * dz

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
