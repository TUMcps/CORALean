import CORALean.ContDynamics.LinProbSys.Operations.InitReachCov
import CORALean.ContDynamics.LinProbSys.Operations.Post
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

/-!
# The covariance CORA's probabilistic reach loop carries

`reach` [1] calls `linProbSys/initReach` for the first step and `post` [2] for every later one,
with the same `pRinput = obj.taylor.pRinput` that `priv_inputSolution` [3] computed once. At a
diagonal `A = diag(l)`, `priv_inputSolution`'s covariance is `initReachCov`; `initReach` starts
`post` from `Rpar_prob = zonotope(pRinput)`, a set, so with the covariance `0`. This is the
covariance of `Rpar_prob` after `k` applications of `post` that carry CORA's `pRinput`, from any
state `st0` that `initReach` could have produced.

## References

* [1] `contDynamics/@contDynamics/reach.m`
* [2] `contDynamics/@linProbSys/post.m`
* [3] `contDynamics/@linProbSys/private/priv_inputSolution.m`
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The covariance of `Rpar_prob` after `k` `post` steps with CORA's `pRinput`. -/
noncomputable def LinProbSys.reachCovCora (sys : LinProbSys n m) (l : Fin n → ℝ) (r : ℝ)
    (st0 : LinProbSys.PostState n) (k : ℕ) : Mat ℝ n n :=
  let pRinput : ProbZonotope n :=
    ⟨Zonotope.ofPoint 0, LinProbSys.initReachCov l sys.C r⟩      -- probZonotope(0,G,gamma)
  ((fun st => (sys.post r pRinput st).1)^[k] st0).Rpar_prob.cov  -- k steps of post

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
