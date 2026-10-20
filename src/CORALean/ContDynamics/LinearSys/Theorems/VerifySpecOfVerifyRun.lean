module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyRun
public import CORALean.ContDynamics.LinearSys.Theorems.VerifySpecOfVerifyStep

@[expose] public section

/-!
# `Alg. 3`'s loop: `true` is sound

Lines 2-27 of [1, Alg. 3]. `verifyRun` returning `some true` means its last iteration passed the
verified test, which `verifySpec_of_verifyStep` turns into the specification; earlier iterations
only shrink `ε_max`.

## Inputs
* `Reach` – reachable set
* `reachFn` – reachable set as a function of the error
* `innerApprox` – inner approximation at an error
* `distG` – distance to a safe polytope
* `distF` – distance to an unsafe polytope
* `le` – comparison oracle on reals
* `G` – safe polytopes
* `F` – unsafe polytopes
* `εmax` – maximal error
* `fuel` – number of iterations

## Hypotheses
* `h` – the oracles are sound
* `hrun` – the run answers true

## Conclusion
* the specification holds

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n r w : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifySpec_of_verifyRun
    {Reach : Set (Vec ℝ n)} {reachFn : ℝ → Zonotope (Vec ℝ n)}
    {innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n)}
    {distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ} {le : ℝ → ℝ → Bool}
    (h : LinearSys.VerifySound Reach reachFn innerApprox distG distF le)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (εmax : ℝ) (fuel : ℕ)
    (hrun : LinearSys.verifyRun reachFn innerApprox distG distF G F le εmax fuel = some true) :
    LinearSys.VerifySpec G F Reach := by -- --- PROOF ---
  induction fuel generalizing εmax with
  | zero => simp [LinearSys.verifyRun] at hrun
  | succ fuel ih =>
    -- name this iteration's verdicts and the shrunk `ε_max`
    simp only [LinearSys.verifyRun] at hrun
    split at hrun
    · -- the until-condition holds: the answer is the verified test itself
      rename_i hcond
      have hv : (le (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νGout 0
          && !le (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νFout 0)
            = true := Option.some.inj hrun
      simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, h.le_iff] at hv
      exact LinearSys.verifySpec_of_verifyStep h G F εmax hv.1 (not_le.1 hv.2)
    · -- no verdict yet: the answer comes from the next iteration
      exact ih _ hrun

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
