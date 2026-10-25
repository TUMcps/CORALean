module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyFloat
public import CORALean.ContDynamics.LinearSys.Definitions.IsVerifySoundFloat
public import CORALean.ContDynamics.LinearSys.Theorems.MaximumFoldToReal
public import CORALean.ContDynamics.LinearSys.Theorems.MinimumFoldToReal

@[expose] public section

/-!
# `verifyFloat` returning `false` refutes the specification

[1, Alg. 3]: under the same hypotheses, `some false` from `verifyFloat` gives a reached state that
violates a safe or an unsafe set.

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
* `hv` – the verification answers false

## Conclusion
* the specification does not hold

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
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

/-- One falsified iteration refutes the specification. -/
theorem LinearSys.aux_not_verifySpecFloat_of_verifyStepFloat
    {Reach : Set (Vec ℝ n)} {reachFn : 𝕋 → Zonotope (Vec 𝕋 n)}
    {innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n)}
    {distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋}
    (h : LinearSys.IsVerifySoundFloat Reach reachFn innerApprox distG distF)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (εmax : 𝕋)
    (hfalse :
      0 < toReal (LinearSys.aux_verifyStepFloat reachFn innerApprox distG distF G F εmax).νGin ∨
      toReal (LinearSys.aux_verifyStepFloat reachFn innerApprox distG distF G F εmax).νFin ≤ 0)
    : -- --- CONCL ---
    ¬ LinearSys.IsVerifySpecFloat G F Reach := by -- --- PROOF ---
  rintro ⟨hGspec, hFspec⟩
  simp only [LinearSys.aux_verifyStepFloat, LinearSys.toReal_maximumFold,
    LinearSys.toReal_minimumFold] at hfalse
  rcases hfalse with hG | hF
  · -- some `distG` is positive, so the inner approximation leaves that safe set
    obtain ⟨j, -, hj⟩ := (Finset.lt_sup'_iff _).1 hG
    exact h.distG_pos _ _ hj ((h.inner _ _).trans (hGspec j))
  · -- some `distF` is nonpositive, so the inner approximation meets that unsafe set
    obtain ⟨j, -, hj⟩ := (Finset.inf'_le_iff _).1 hF
    exact h.distF_nonpos _ _ hj ((hFspec j).mono_left (h.inner _ _))


/-- A `false` from the float verification loop refutes the specification. -/
theorem LinearSys.aux_not_verifySpecFloat_of_verifyRunFloat
    {Reach : Set (Vec ℝ n)} {reachFn : 𝕋 → Zonotope (Vec 𝕋 n)}
    {innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n)}
    {distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋}
    (h : LinearSys.IsVerifySoundFloat Reach reachFn innerApprox distG distF)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n))
    (εmax : 𝕋) (fuel : ℕ)
    (hrun : LinearSys.aux_verifyRunFloat reachFn innerApprox distG distF G F εmax fuel = some false)
    : -- --- CONCL ---
    ¬ LinearSys.IsVerifySpecFloat G F Reach := by -- --- PROOF ---
  induction fuel generalizing εmax with
  | zero => simp [LinearSys.aux_verifyRunFloat] at hrun
  | succ fuel ih =>
    simp only [LinearSys.aux_verifyRunFloat] at hrun
    split at hrun
    · -- the until-condition holds with the verified test false, so the falsified test is true
      rename_i hcond
      have hv : (le (LinearSys.aux_verifyStepFloat reachFn innerApprox distG distF G F εmax).νGout
          zero && ltStrict zero
            (LinearSys.aux_verifyStepFloat reachFn innerApprox distG distF G F εmax).νFout) = false
              :=
        Option.some.inj hrun
      rw [hv] at hcond
      simp only [Bool.false_or, Bool.or_eq_true] at hcond
      refine LinearSys.aux_not_verifySpecFloat_of_verifyStepFloat h G F εmax ?_
      rcases hcond with hc | hc
      · exact Or.inl (by simpa [toReal_zero] using toReal_lt_of_ltStrict hc)
      · exact Or.inr (by simpa [toReal_zero] using toReal_le_of_le hc)
    · -- no verdict yet: the answer comes from the next iteration
      exact ih _ hrun


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifyFloat_violated
    {Reach : Set (Vec ℝ n)} {reachFn : 𝕋 → Zonotope (Vec 𝕋 n)}
    {innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n)}
    {distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋}
    (h : LinearSys.IsVerifySoundFloat Reach reachFn innerApprox distG distF)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n))
    (εmax₀ : 𝕋) (fuel : ℕ)
    (hv : LinearSys.verifyFloat reachFn innerApprox distG distF G F εmax₀ fuel = some false)
    :
    ¬ LinearSys.IsVerifySpecFloat G F Reach :=
  LinearSys.aux_not_verifySpecFloat_of_verifyRunFloat h G F εmax₀ fuel hv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
