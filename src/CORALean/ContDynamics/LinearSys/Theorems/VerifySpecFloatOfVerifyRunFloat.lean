import CORALean.ContDynamics.LinearSys.Operations.VerifyRunFloat
import CORALean.ContDynamics.LinearSys.Theorems.VerifySpecFloatOfVerifyStepFloat

/-!
# A `true` from the float verification loop proves the specification

[1, Alg. 3]: `some true` from `verifyRunFloat` means some iteration's verified test passed, the
comparison `le` certifying `ν̂_G ≤ 0` and `ltStrict` certifying `ν̂_F > 0`; the loop's other
iterations only shrink `ε_max`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r w : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifySpecFloat_of_verifyRunFloat
    {Reach : Set (Vec ℝ n)} {reachFn : 𝕋 → Zonotope (Vec 𝕋 n)}
    {innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n)}
    {distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋}
    (h : LinearSys.VerifySoundFloat Reach reachFn innerApprox distG distF)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n))
    (εmax : 𝕋) (fuel : ℕ)
    (hrun : LinearSys.verifyRunFloat reachFn innerApprox distG distF G F εmax fuel = some true) :
    LinearSys.VerifySpecFloat G F Reach := by -- --- PROOF ---
  induction fuel generalizing εmax with
  | zero => simp [LinearSys.verifyRunFloat] at hrun
  | succ fuel ih =>
    simp only [LinearSys.verifyRunFloat] at hrun
    split at hrun
    · -- the until-condition holds: the answer is the verified test itself
      rename_i hcond
      have hv : (le (LinearSys.verifyStepFloat reachFn innerApprox distG distF G F εmax).1.νGout
          zero && ltStrict zero
            (LinearSys.verifyStepFloat reachFn innerApprox distG distF G F εmax).1.νFout) = true :=
        Option.some.inj hrun
      rw [Bool.and_eq_true] at hv
      refine LinearSys.verifySpecFloat_of_verifyStepFloat h G F εmax ?_ ?_
      · simpa [toReal_zero] using toReal_le_of_le hv.1
      · simpa [toReal_zero] using toReal_lt_of_ltStrict hv.2
    · -- no verdict yet: the answer comes from the next iteration
      exact ih _ hrun

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
