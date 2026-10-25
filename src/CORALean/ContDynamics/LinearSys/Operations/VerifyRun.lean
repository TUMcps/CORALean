module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyStep

@[expose] public section

/-!
# `Alg. 3` lines 2-27: the loop

`verifyRun`: [1, Alg. 3] lines 2-27, iterate `verifyStep` until the until-condition of line 26
holds, returning line 27's verdict; `none` where `fuel` iterations were not enough. `[1]`
gives no bound on `Alg. 3`'s own repeat count (`Thm. 1` is about `Alg. 2`), so `verifyRun`
needs `fuel`.

## Inputs
* `reachFn` – reachable set as a function of the error
* `innerApprox` – inner approximation at an error
* `distG` – distance to a safe polytope
* `distF` – distance to an unsafe polytope
* `G` – safe polytopes
* `F` – unsafe polytopes
* `le` – comparison oracle on reals
* `εmax` – maximal error

## Output
* verdict after a given number of iterations

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n r w : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 2-27: iterate `verifyStep` until the until-condition of line 26 holds, returning
line 27's verdict; `none` where `fuel` iterations were not enough. -/
noncomputable def LinearSys.verifyRun (reachFn : ℝ → Zonotope (Vec ℝ n))
    (innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n))
    (distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (le : ℝ → ℝ → Bool) (εmax : ℝ) : ℕ → Option Bool
  | 0 => none
  | fuel + 1 =>
    let (it, εmax') :=
      LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax        -- 3.-25.
    let verified := le it.νGout 0 && !(le it.νFout 0)                         -- 27. (bνG≤0)∧(bνF>0)
    let falsified := !(le it.νGin 0) || le it.νFin 0                          -- 26. (qνG>0)∨(qνF≤0)
    if verified || falsified then some verified                     -- 26. until, 27. return
    else LinearSys.verifyRun reachFn innerApprox distG distF G F le εmax' fuel -- 2. repeat

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
