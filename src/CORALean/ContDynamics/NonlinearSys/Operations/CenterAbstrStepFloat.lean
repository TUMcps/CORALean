module

public import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepFloat

@[expose] public section

/-!
# `Alg. 1` lines 3-15, linearizing at the center, in floats

`step_centerAbstrStep` in `𝕋` from a `FloatModel`: [1, Alg. 1] linearizes at the center of the set
the step starts from, `z✱(t_s) = center(R(t_s))` with `center(U)` for the input half, where
`relinStepFloat` linearizes at [2, (6)]'s half step further along `f`. The rest is
`relinStepAtFloat`: the region first and checked, then the slopes of the model over it in place of
the `taylor` call and the abstraction-error loop of lines 4-10, then one step of the linearized
system. It returns `R(τ_s)` and `R(t_{s+1})`.

## Inputs
* `fm` – float model
* `U` – input zonotope
* `options` – reachability options
* `R` – start set

## Output
* the time-interval set and the end set of the step, or none

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for Reachability
      Analysis of Nonlinear Systems". Proceedings of the 24th International Conference on Hybrid
      Systems: Computation and Control,
      2021.](../../../../../references/2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md)
* [2] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(R(τ_s), R(t_{s+1}))` from `R = R(t_s)` under inputs in `U`, linearized at the
center of `R`, or `none` if the region check or the linear step fails. -/
def NonlinearSys.FloatModel.centerAbstrStepFloat (fm : NonlinearSys.FloatModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachOptions 𝕋) (R : Zonotope (Vec 𝕋 n)) :
    Option (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) :=
  let xs := R.c                                                     -- 3. z✱(t_s) ← center(R(t_s))
  fm.relinStepAtFloat U options R xs                                -- 4.-15. the step at z✱

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
