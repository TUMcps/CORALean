module

public import CORALean.ContDynamics.NonlinearSys.Operations.CenterAbstrStepFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinRunFloat

@[expose] public section

/-!
# `Alg. 1`'s loop, linearizing at the center, in floats

`centerAbstrStepFloat` iterated `k` times, the set a step reaches at its end being the set the
next one starts from — the while loop of [1, Alg. 1] — collecting each step's set over its whole
interval. One failed step fails the run.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
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

/-- `R(τ_0), …, R(τ_{k-1})` of `k` steps linearized at the center, from `R`, or `none` if
one of them fails. -/
def NonlinearSys.FloatModel.centerAbstrRunFloat (fm : NonlinearSys.FloatModel 𝕋 n m)
    (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachOptions 𝕋) :
    ℕ → Zonotope (Vec 𝕋 n) → Option (List (Zonotope (Vec 𝕋 n))) :=
  fm.relinRunAtFloat U options fun R => R.c                         -- 3. z✱(t_s) ← center(R(t_s))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
