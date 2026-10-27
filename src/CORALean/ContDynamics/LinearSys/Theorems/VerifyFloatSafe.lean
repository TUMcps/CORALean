module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyFloat
public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifySoundFloat
public import CORALean.ContDynamics.LinearSys.Theorems.MaximumFoldToReal
public import CORALean.ContDynamics.LinearSys.Theorems.MinimumFoldToReal
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# `verifyFloat` returning `true` proves the specification

[1, Alg. 3]: if `reachFn` is outer, `innerApprox` inner and the distances mean containment and
meeting, `some true` from `verifyFloat` gives the safe and unsafe sets on all reached states.

## Inputs
* `Reach` – reachable set
* `reachFn` – float reachable set as a function of the error
* `innerApprox` – float inner approximation at an error
* `distG` – distance to a safe polytope
* `distF` – distance to an unsafe polytope
* `G` – float safe polytopes
* `F` – float unsafe polytopes
* `εmax₀` – float initial maximal error
* `fuel` – number of iterations

## Hypotheses
* `h` – the oracles are sound
* `hv` – the verification answers true

## Conclusion
* the specification holds

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n r w : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One verified iteration proves the specification. -/
private theorem LinearSys.aux_isVerifySpecFloat_of_verifyStepFloat
    {Reach : Set (Vec ℝ n)} {reachFn : 𝕋 → Zonotope (Vec 𝕋 n)}
    {innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n)}
    {distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋}
    (h : LinearSys.IsVerifySoundFloat Reach reachFn innerApprox distG distF)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (εmax : 𝕋)
    (hG : toReal
      (LinearSys.step_verifyStepFloat reachFn innerApprox distG distF G F εmax).νGout ≤ 0)
    (hF : 0 < toReal
      (LinearSys.step_verifyStepFloat reachFn innerApprox distG distF G F εmax).νFout)
    : -- --- CONCL ---
    LinearSys.IsVerifySpecFloat G F Reach := by -- --- PROOF ---
  -- the outer approximation, read as a constrained zonotope, still contains `Reach`
  have hR : Reach ⊆ (reachFn εmax).conZonotope.construct :=
    (h.outer εmax).trans (Zonotope.conZonotope_contains _)
  simp only [LinearSys.step_verifyStepFloat, LinearSys.toReal_maximumFold,
    LinearSys.toReal_minimumFold] at hG hF
  refine ⟨fun j => ?_, fun j => ?_⟩
  · -- every `distG` is below the maximum, hence `≤ 0`
    have hj := (Finset.sup'_le_iff _ _).1 hG j (Finset.mem_univ j)
    exact hR.trans (h.distG_nonpos _ _ hj)
  · -- every `distF` is above the minimum, hence `> 0`
    have hj := (Finset.lt_inf'_iff _).1 hF j (Finset.mem_univ j)
    exact (h.distF_pos _ _ hj).mono_left hR


/-- A `true` from the float verification loop proves the specification. -/
private theorem LinearSys.aux_isVerifySpecFloat_of_verifyRunFloat
    {Reach : Set (Vec ℝ n)} {reachFn : 𝕋 → Zonotope (Vec 𝕋 n)}
    {innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n)}
    {distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋}
    (h : LinearSys.IsVerifySoundFloat Reach reachFn innerApprox distG distF)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n))
    (εmax : 𝕋) (fuel : ℕ)
    (hrun : LinearSys.step_verifyRunFloat reachFn innerApprox distG distF G F εmax fuel = some true)
    : -- --- CONCL ---
    LinearSys.IsVerifySpecFloat G F Reach := by -- --- PROOF ---
  induction fuel generalizing εmax with
  | zero => simp [LinearSys.step_verifyRunFloat] at hrun
  | succ fuel ih =>
    simp only [LinearSys.step_verifyRunFloat] at hrun
    split at hrun
    · -- the until-condition holds: the answer is the verified test itself
      rename_i hcond
      have hv : (le (LinearSys.step_verifyStepFloat reachFn innerApprox distG distF G F εmax).νGout
          zero && ltStrict zero
            (LinearSys.step_verifyStepFloat reachFn innerApprox distG distF G F εmax).νFout) = true
              :=
        Option.some.inj hrun
      rw [Bool.and_eq_true] at hv
      refine LinearSys.aux_isVerifySpecFloat_of_verifyStepFloat h G F εmax ?_ ?_
      · simpa [toReal_zero] using toReal_le_of_le hv.1
      · simpa [toReal_zero] using toReal_lt_of_ltStrict hv.2
    · -- no verdict yet: the answer comes from the next iteration
      exact ih _ hrun


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifyFloat_safe
    {Reach : Set (Vec ℝ n)} {reachFn : 𝕋 → Zonotope (Vec 𝕋 n)}
    {innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n)}
    {distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋}
    (h : LinearSys.IsVerifySoundFloat Reach reachFn innerApprox distG distF)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n))
    (εmax₀ : 𝕋) (fuel : ℕ)
    (hv : LinearSys.verifyFloat reachFn innerApprox distG distF G F εmax₀ fuel = some true)
    :
    LinearSys.IsVerifySpecFloat G F Reach :=
  LinearSys.aux_isVerifySpecFloat_of_verifyRunFloat h G F εmax₀ fuel hv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
