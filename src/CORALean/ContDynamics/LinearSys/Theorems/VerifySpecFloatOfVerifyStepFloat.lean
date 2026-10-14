module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyStepFloat
public import CORALean.ContDynamics.LinearSys.Definitions.VerifySoundFloat
public import CORALean.ContDynamics.LinearSys.Theorems.MaximumFoldToReal
public import CORALean.ContDynamics.LinearSys.Theorems.MinimumFoldToReal
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# One verified iteration proves the specification

[1, Alg. 3], lines 3-24: when an iteration's `ν̂_G` is at most `0` and its `ν̂_F` positive, the
exact reachable set satisfies every safe and unsafe set. The outer approximation, read as a
constrained zonotope, still contains `Reach`, every `distG` is below the maximum and every `distF`
above the minimum.

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

theorem LinearSys.verifySpecFloat_of_verifyStepFloat
    {Reach : Set (Vec ℝ n)} {reachFn : 𝕋 → Zonotope (Vec 𝕋 n)}
    {innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n)}
    {distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋}
    (h : LinearSys.VerifySoundFloat Reach reachFn innerApprox distG distF)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (εmax : 𝕋)
    (hG : toReal (LinearSys.verifyStepFloat reachFn innerApprox distG distF G F εmax).1.νGout ≤ 0)
    (hF : 0 < toReal (LinearSys.verifyStepFloat reachFn innerApprox distG distF G F εmax).1.νFout) :
    LinearSys.VerifySpecFloat G F Reach := by -- --- PROOF ---
  -- the outer approximation, read as a constrained zonotope, still contains `Reach`
  have hR : Reach ⊆ (reachFn εmax).conZonotope.construct :=
    (h.outer εmax).trans (Zonotope.conZonotope_contains _)
  simp only [LinearSys.verifyStepFloat, LinearSys.toReal_maximumFold,
    LinearSys.toReal_minimumFold] at hG hF
  refine ⟨fun j => ?_, fun j => ?_⟩
  · -- every `distG` is below the maximum, hence `≤ 0`
    have hj := (Finset.sup'_le_iff _ _).1 hG j (Finset.mem_univ j)
    exact hR.trans (h.distG_nonpos _ _ hj)
  · -- every `distF` is above the minimum, hence `> 0`
    have hj := (Finset.lt_inf'_iff _).1 hF j (Finset.mem_univ j)
    exact (h.distF_pos _ _ hj).mono_left hR

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
