module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyStepFloat
public import CORALean.ContDynamics.LinearSys.Definitions.VerifySoundFloat
public import CORALean.ContDynamics.LinearSys.Theorems.MaximumFoldToReal
public import CORALean.ContDynamics.LinearSys.Theorems.MinimumFoldToReal

@[expose] public section

/-!
# One falsified iteration refutes the specification

[1, Alg. 3], lines 5-16: when an iteration's `ν̌_G` is positive or its `ν̌_F` at most `0`, the
exact reachable set violates a safe or an unsafe set, since the inner approximation, which it
contains, does.

## Inputs
* `Reach` – reachable set
* `reachFn` – float reachable set as a function of the error
* `innerApprox` – float inner approximation at an error
* `distG` – distance to a safe polytope
* `distF` – distance to an unsafe polytope
* `G` – float safe polytopes
* `F` – float unsafe polytopes
* `εmax` – float maximal error

## Hypotheses
* `h` – the oracles are sound
* `hfalse` – the iteration's distance test fails

## Conclusion
* the specification does not hold

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

theorem LinearSys.not_verifySpecFloat_of_verifyStepFloat
    {Reach : Set (Vec ℝ n)} {reachFn : 𝕋 → Zonotope (Vec 𝕋 n)}
    {innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n)}
    {distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋}
    (h : LinearSys.VerifySoundFloat Reach reachFn innerApprox distG distF)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (εmax : 𝕋)
    (hfalse :
      0 < toReal (LinearSys.verifyStepFloat reachFn innerApprox distG distF G F εmax).1.νGin ∨
      toReal (LinearSys.verifyStepFloat reachFn innerApprox distG distF G F εmax).1.νFin ≤ 0)
    : -- --- CONCL ---
    ¬ LinearSys.VerifySpecFloat G F Reach := by -- --- PROOF ---
  rintro ⟨hGspec, hFspec⟩
  simp only [LinearSys.verifyStepFloat, LinearSys.toReal_maximumFold,
    LinearSys.toReal_minimumFold] at hfalse
  rcases hfalse with hG | hF
  · -- some `distG` is positive, so the inner approximation leaves that safe set
    obtain ⟨j, -, hj⟩ := (Finset.lt_sup'_iff _).1 hG
    exact h.distG_pos _ _ hj ((h.inner _ _).trans (hGspec j))
  · -- some `distF` is nonpositive, so the inner approximation meets that unsafe set
    obtain ⟨j, -, hj⟩ := (Finset.inf'_le_iff _).1 hF
    exact h.distF_nonpos _ _ hj ((hFspec j).mono_left (h.inner _ _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
