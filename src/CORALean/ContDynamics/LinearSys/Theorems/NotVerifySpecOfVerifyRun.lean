module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyRun
public import CORALean.ContDynamics.LinearSys.Theorems.NotVerifySpecOfVerifyStep

@[expose] public section

/-!
# `Alg. 3`'s loop: `false` is sound

Lines 2-27 of [1, Alg. 3]. `verifyRun` returning `some false` means its last iteration passed the
falsified test and not the verified one, which `not_verifySpec_of_verifyStep` turns into a
violation.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n r w : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.not_verifySpec_of_verifyRun
    {Reach : Set (Vec ℝ n)} {reachFn : ℝ → Zonotope (Vec ℝ n)}
    {innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n)}
    {distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ} {le : ℝ → ℝ → Bool}
    (h : LinearSys.VerifySound Reach reachFn innerApprox distG distF le)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (εmax : ℝ) (fuel : ℕ)
    (hrun : LinearSys.verifyRun reachFn innerApprox distG distF G F le εmax fuel = some false) :
    ¬ LinearSys.VerifySpec G F Reach := by -- --- PROOF ---
  induction fuel generalizing εmax with
  | zero => simp [LinearSys.verifyRun] at hrun
  | succ fuel ih =>
    simp only [LinearSys.verifyRun] at hrun
    split at hrun
    · -- the until-condition holds with the verified test false, so the falsified test is true
      rename_i hcond
      have hv : (le (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νGout 0
          && !le (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νFout 0)
            = false := Option.some.inj hrun
      rw [hv] at hcond
      simp only [Bool.false_or, Bool.or_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
        h.le_iff, not_le] at hcond
      exact LinearSys.not_verifySpec_of_verifyStep h G F εmax hcond
    · -- no verdict yet: the answer comes from the next iteration
      exact ih _ hrun

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
