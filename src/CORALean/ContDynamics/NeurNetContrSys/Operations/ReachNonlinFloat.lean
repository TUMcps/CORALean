module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.AppendU2X
public import CORALean.ContDynamics.NeurNetContrSys.Operations.AugmentNonlin
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachLoopFloat
public import CORALean.ContSet.Zonotope.Float.Operations.Project
public import CORALean.ContSet.Zonotope.Float.Operations.Reduce
public import CORALean.Global.StepOf

@[expose] public section

/-!
# A neural-network-controlled nonlinear plant, reached in floats: `neurNetContrSys/reach`

CORA's `neurNetContrSys/reach` at a `nonlinearSys` and zonotopes, in `𝕋`. Each control period
joins the state set with the network's image (`jt`, CORA's `evaluate_` and `aux_appendU2X`), runs
`N` steps of `linReachLoopFloat` of the augmented plant `augmentNonlin` from it, each handing its
abstraction error to the next, the first guessing from zero (`initReach`), each end set reduced
to order `ρ` (`post`), and projects the end set to the plant's states; the next period starts
from it. The network's part is the caller's `jt`, `NeurNetContrSys.joint` of the layers'
image for a network (`reachClosedLoopFloat_outer` holds it to `[x; π(x)]`); `maxError` is none,
as CORA refuses a split. `none` is returned where `jt` or a step fails.

## Inputs
* `fm` – float Hessian model of the augmented plant
* `jt` – joint enclosure of a state and the network's output
* `U_ext` – external input zonotope
* `options` – reachability options of one step, `N` of which are one control period
* `N` – steps per period
* `enlarge` – enlargement of the error, CORA's `1.1`
* `fuel` – iteration bound of each step's loop
* `step` – linear step
* `X₀` – initial zonotope

## Output
* the set at the end of the last control period, or none

## References

* [1] [N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715,
      2022.](../../../../../references/2022/kochdumper-arxiv-nn-polyzono.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m e : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The set at the end of `k` loop steps from `R`, each guessing from the last one's error `err`,
or `none` if one of them fails. -/
@[step_of NonlinearSys.FloatHessModel.reachClosedLoopFloat]
def NonlinearSys.FloatHessModel.step_linReachLoopEndFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachFloatOptions 𝕋) (enlarge : 𝕋) (fuel : ℕ)
    (step : NonlinearSys.LinearStep) :
    ℕ → Zonotope (Vec 𝕋 n) → Vec 𝕋 n → Option (Zonotope (Vec 𝕋 n))
  | 0, R, _ => some R
  | k + 1, R, err => do
    let S ← fm.linReachLoopFloat U options enlarge fuel R err none step  -- (R(τ), R(t+Δt), err)
    fm.step_linReachLoopEndFloat U options enlarge fuel step k (S.2.1.reduce options.ρ) S.2.2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] over `H` control periods from `X₀` at the augmented plant `fm` of `n` states and
`m` network outputs: the set at the end of the last, or `none`. -/
def NonlinearSys.FloatHessModel.reachClosedLoopFloat
    (fm : NonlinearSys.FloatHessModel 𝕋 (n + m) e)
    (jt : Zonotope (Vec 𝕋 n) → Option (Zonotope (Vec 𝕋 (n + m))))
    (U_ext : Zonotope (Vec 𝕋 e)) (options : LinearSys.ReachFloatOptions 𝕋) (N : ℕ)
    (enlarge : 𝕋) (fuel : ℕ) (step : NonlinearSys.LinearStep) (X₀ : Zonotope (Vec 𝕋 n)) :
    ℕ → Option (Zonotope (Vec 𝕋 n))
  -- 1. `R(t₀) ← X₀`
  | 0 => some X₀
  | i + 1 => do
    -- the loop so far, `i` cycles
    let X ← fm.reachClosedLoopFloat jt U_ext options N enlarge fuel step X₀ i
    -- 3-4. the joint set of `X` and the network's image `Y`, `R̂(tᵢ) ← R(tᵢ) × Y`
    let J ← jt X
    -- 6. `R̂(tᵢ₊₁)` by the reachable-set step, `N` loop steps
    let Z ← fm.step_linReachLoopEndFloat U_ext options enlarge fuel step N J (fun _ => zero)
    -- 7. project back, `R(tᵢ₊₁) ← proj(R̂(tᵢ₊₁))`
    pure (Z.project (Fin.castAdd m))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
