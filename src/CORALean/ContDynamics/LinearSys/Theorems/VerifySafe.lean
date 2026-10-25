module

public import CORALean.ContDynamics.LinearSys.Operations.Verify
public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifySound
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConZonotopeExact

@[expose] public section

/-!
# [1, Alg. 3]: `verify` answering `true` is sound

Relative to what the passed-in functions promise (`IsVerifySound`): where `verify` returns
`some true`, every safe set contains and every unsafe set misses all states reached by a
trajectory. `none` (fuel exhausted) claims nothing.

## Inputs
* `Reach` – reachable set
* `reachFn` – reachable set as a function of the error
* `innerApprox` – inner approximation at an error
* `distG` – distance to a safe polytope
* `distF` – distance to an unsafe polytope
* `le` – comparison oracle on reals
* `G` – safe polytopes
* `F` – unsafe polytopes
* `εmax₀` – initial maximal error
* `fuel` – number of iterations

## Hypotheses
* `h` – the oracles are sound
* `hv` – the verification answers true

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A safe verdict of one iteration of `Alg. 3` proves the specification. -/
theorem LinearSys.aux_verifySpec_of_verifyStep {Reach : Set (Vec ℝ n)}
    {reachFn : ℝ → Zonotope (Vec ℝ n)}
    {innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n)}
    {distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ}
    {le : ℝ → ℝ → Bool} (h : LinearSys.IsVerifySound Reach reachFn innerApprox distG distF le)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n)) (εmax : ℝ)
    (hG : (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νGout ≤ 0)
    (hF : 0 < (LinearSys.verifyStep reachFn innerApprox distG distF G F le εmax).1.νFout)
    : -- --- CONCL ---
    LinearSys.IsVerifySpec G F Reach := by -- --- PROOF ---
  -- the outer approximation, read as a constrained zonotope, still contains `Reach`
  have hR : Reach ⊆ (reachFn εmax).conZonotope.construct :=
    (Zonotope.conZonotope_exact (reachFn εmax)) ▸ h.outer εmax
  simp only [LinearSys.verifyStep] at hG hF
  refine ⟨fun j => ?_, fun j => ?_⟩
  · -- every `distG` is below the supremum, hence `≤ 0`
    have hj := (Finset.sup'_le_iff _ _).1 hG j (Finset.mem_univ j)
    exact hR.trans (h.distG_nonpos _ _ hj)
  · -- every `distF` is above the infimum, hence `> 0`
    have hj := (Finset.lt_inf'_iff _).1 hF j (Finset.mem_univ j)
    exact (h.distF_pos _ _ hj).mono_left hR


/-- A `true` from the verification loop of `Alg. 3` proves the specification. -/
theorem LinearSys.aux_verifySpec_of_verifyRun
    {Reach : Set (Vec ℝ n)} {reachFn : ℝ → Zonotope (Vec ℝ n)}
    {innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n)}
    {distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ} {le : ℝ → ℝ → Bool}
    (h : LinearSys.IsVerifySound Reach reachFn innerApprox distG distF le)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (εmax : ℝ) (fuel : ℕ)
    (hrun : LinearSys.verifyRun reachFn innerApprox distG distF G F le εmax fuel = some true)
    : -- --- CONCL ---
    LinearSys.IsVerifySpec G F Reach := by -- --- PROOF ---
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
      exact LinearSys.aux_verifySpec_of_verifyStep h G F εmax hv.1 (not_le.1 hv.2)
    · -- no verdict yet: the answer comes from the next iteration
      exact ih _ hrun


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verify_safe
    {Reach : Set (Vec ℝ n)} {reachFn : ℝ → Zonotope (Vec ℝ n)}
    {innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n)}
    {distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ} {le : ℝ → ℝ → Bool}
    (h : LinearSys.IsVerifySound Reach reachFn innerApprox distG distF le)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (εmax₀ : ℝ) (fuel : ℕ)
    (hv : LinearSys.verify reachFn innerApprox distG distF G F le εmax₀ fuel = some true)
    :
    LinearSys.IsVerifySpec G F Reach :=
  LinearSys.aux_verifySpec_of_verifyRun h G F εmax₀ fuel hv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
