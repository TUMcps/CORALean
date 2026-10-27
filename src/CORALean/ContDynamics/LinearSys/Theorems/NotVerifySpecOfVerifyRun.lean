module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyRun
public import CORALean.ContDynamics.LinearSys.Operations.VerifyStep
public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifySound

@[expose] public section

/-!
# `Alg. 3`'s loop: `false` is sound

Lines 2-27 of [1, Alg. 3]. `verifyRun` returning `some false` means its last iteration passed the
falsified test and not the verified one, which `aux_not_isVerifySpec_of_verifyStep` turns into a
violation.

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
* `hrun` – the run answers false

## Conclusion
* the specification does not hold

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n r w : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem LinearSys.aux_not_isVerifySpec_of_verifyStep {Reach : Set (Vec ℝ n)}
    {reachFn : ℝ → Zonotope (Vec ℝ n)}
    {innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n)}
    {distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ}
    {le : ℝ → ℝ → Bool} (h : LinearSys.IsVerifySound Reach reachFn innerApprox distG distF le)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n)) (εmax : ℝ)
    (hfalse :
      0 < (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νGin ∨
      (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νFin ≤ 0)
    : -- --- CONCL ---
    ¬ LinearSys.IsVerifySpec G F Reach := by -- --- PROOF ---
  rintro ⟨hGspec, hFspec⟩
  simp only [LinearSys.verifyStep] at hfalse
  rcases hfalse with hG | hF
  · -- some `distG` is positive, so the inner approximation leaves that safe set
    obtain ⟨j, -, hj⟩ := (Finset.lt_sup'_iff _).1 hG
    exact h.distG_pos _ _ hj ((h.inner _ _).trans (hGspec j))
  · -- some `distF` is nonpositive, so the inner approximation meets that unsafe set
    obtain ⟨j, -, hj⟩ := (Finset.inf'_le_iff _).1 hF
    exact h.distF_nonpos _ _ hj ((hFspec j).mono_left (h.inner _ _))


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.not_isVerifySpec_of_verifyRun
    {Reach : Set (Vec ℝ n)} {reachFn : ℝ → Zonotope (Vec ℝ n)}
    {innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n)}
    {distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ} {le : ℝ → ℝ → Bool}
    (h : LinearSys.IsVerifySound Reach reachFn innerApprox distG distF le)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (εmax : ℝ) (fuel : ℕ)
    (hrun : LinearSys.verifyRun reachFn innerApprox distG distF G F le εmax fuel = some false)
    : -- --- CONCL ---
    ¬ LinearSys.IsVerifySpec G F Reach := by -- --- PROOF ---
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
      exact LinearSys.aux_not_isVerifySpec_of_verifyStep h G F εmax hcond
    · -- no verdict yet: the answer comes from the next iteration
      exact ih _ hrun

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
