import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepFloat

/-!
# `Alg. 1` lines 3-15, linearizing at the centre, in floats

`centreAbstrStep` in `𝕋` from a `FloatModel`: [1, Alg. 1] linearizes at the centre of the set the
step starts from, `z✱(t_s) = center(R(t_s))` with `center(U)` for the input half, where
`relinStepFloat` linearizes at [2, (6)]'s half step further along `f`. The rest is
`relinStepAtFloat`: the region first and checked, then the slopes of the model over it in place of
the `taylor` call and the abstraction-error loop of lines 4-10, then one step of the linearized
system. It returns `R(τ_s)` and `R(t_{s+1})`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
* [2] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(R(τ_s), R(t_{s+1}))` from `R = R(t_s)` under inputs in `U`, linearized at the
centre of `R`, or `none` if the region check or the linear step fails. -/
def NonlinearSys.FloatModel.centreAbstrStepFloat (fm : NonlinearSys.FloatModel 𝕋 n m)
    (U : Zonotope 𝕋 m) (options : LinearSys.ReachOptions 𝕋) (R : Zonotope 𝕋 n) :
    Option (Zonotope 𝕋 n × Zonotope 𝕋 n) :=
  let xs := R.c                                                     -- 3. z✱(t_s) ← center(R(t_s))
  fm.relinStepAtFloat U options R xs                                -- 4.-15. the step at z✱

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
