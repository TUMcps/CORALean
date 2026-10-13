import CORALean.ContDynamics.NonlinearSys.Operations.AdaptStepFloat

/-!
# The adaptive loop of `Alg. 1`, in floats

`adaptStepFloat` iterated while `t_k < t_end`, as [1, Alg. 1]'s line 2 does, at most `k` times.
Where the real `adaptRun` returns the state after `k` iterations, this returns every state the
iterations produced, in order: each carries the window `R(τ_k)` that the run's guarantee is about.
One failed step fails the run.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The states of at most `k` adaptively-tuned steps from `s`, while `t < t_end`, or `none`
if one of them fails. -/
def NonlinearSys.FloatHessModel.adaptRunFloat [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (U : Zonotope (Vec 𝕋 m))
    (options : LinearSys.ReachOptions 𝕋) (ζδ ζh ζZ ζK : 𝕋) (prec bis fuel : ℕ) (tend : ℚ) :
    ℕ → NonlinearSys.AdaptState (fun k => Zonotope (Vec 𝕋 k)) n ℚ 𝕋 →
      Option (List (NonlinearSys.AdaptState (fun k => Zonotope (Vec 𝕋 k)) n ℚ 𝕋))
  | 0, _ => some []
  | k + 1, s =>
    if s.t < tend                                                   -- 2. while t_k < t_end
    then do
      let s' ← fm.adaptStepFloat U options ζδ ζh ζZ ζK prec bis fuel s  -- 3.-18. one step
      let rest ← fm.adaptRunFloat U options ζδ ζh ζZ ζK prec bis fuel tend k s'  -- the steps after
      pure (s' :: rest)
    else some []

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
