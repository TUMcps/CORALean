import CORALean.ContDynamics.LinearSys.Operations.VerifyRunFloat

/-!
# `Alg. 3` line 1: automated verification, in floats

`verifyFloat`: `some true` where the specification given by the safe sets `G` and unsafe sets `F`
is verified, `some false` where it is falsified, `none` where `fuel` repeat-until iterations did
not reach a verdict. Line 1's "estimated from simulations" is left a parameter, `ε_max₀`. Soundness
is `verifyFloat_safe` and `verifyFloat_violated`.

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

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n r w : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: `true` where the specification is verified, `false` where it is falsified. -/
def LinearSys.verifyFloat (reachFn : 𝕋 → Zonotope (Vec 𝕋 n))
    (innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n))
    (distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (εmax₀ : 𝕋)
    (fuel : ℕ) : Option Bool :=
  LinearSys.verifyRunFloat reachFn innerApprox distG distF G F εmax₀ fuel       -- 1. ε_max ← ε_max₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
