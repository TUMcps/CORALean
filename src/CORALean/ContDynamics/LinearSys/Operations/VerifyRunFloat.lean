module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyStepFloat

@[expose] public section

/-!
# The verification loop, in floats

Lines 2-27 of [1, Alg. 3]: iterate `verifyStepFloat` until the until-condition of line 26
holds, returning line 27's verdict; `none` where `fuel` iterations were not enough. A float
comparison is only trusted when it answers `true`, so the tests are written for that: verified
is `ν̂_G ≤ 0` and `ν̂_F` certified positive (`ltStrict`), falsified is `ν̌_G` certified positive or
`ν̌_F ≤ 0`. Where a comparison cannot be certified the loop runs on, to `none` at worst.

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

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n r w : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSys.verifyRunFloat (reachFn : 𝕋 → Zonotope (Vec 𝕋 n))
    (innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n))
    (distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (εmax : 𝕋) :
    ℕ → Option Bool
  | 0 => none
  | fuel + 1 =>
    let (it, εmax') :=
      LinearSys.verifyStepFloat reachFn innerApprox distG distF G F εmax      -- 3.-25.
    let verified := le it.νGout zero && ltStrict zero it.νFout                -- 27. (bνG≤0)∧(bνF>0)
    let falsified := ltStrict zero it.νGin || le it.νFin zero                 -- 26. (qνG>0)∨(qνF≤0)
    if verified || falsified then some verified                               -- 26. until, 27.
    else LinearSys.verifyRunFloat reachFn innerApprox distG distF G F εmax' fuel -- 2. repeat

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
