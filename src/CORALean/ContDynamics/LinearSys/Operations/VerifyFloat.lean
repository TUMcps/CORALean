module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyIterFloat
public import CORALean.ContDynamics.LinearSys.Operations.MaximumFold
public import CORALean.ContDynamics.LinearSys.Operations.MinimumFold
public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.HPolytope.Float.Instances
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Alg. 3` line 1: automated verification, in floats

`verifyFloat`: `some true` where the specification given by the safe sets `G` and unsafe sets `F`
is verified, `some false` where it is falsified, `none` where `fuel` repeat-until iterations did
not reach a verdict. Line 1's "estimated from simulations" is left a parameter, `ε_max₀`. Soundness
is `verifyFloat_safe` and `verifyFloat_violated`.

## Inputs
* `reachFn` – float reachable set as a function of the error
* `innerApprox` – float inner approximation at an error
* `distG` – distance to a safe polytope
* `distF` – distance to an unsafe polytope
* `G` – float safe polytopes
* `F` – float unsafe polytopes
* `εmax₀` – float initial maximal error
* `fuel` – number of iterations

## Output
* verdict: verified, falsified, or undecided

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n r w : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

section
open FloatOps

@[step_of LinearSys.verifyFloat]
def LinearSys.step_verifyStepFloat (reachFn : 𝕋 → Zonotope (Vec 𝕋 n))
    (innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n))
    (distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (εmax : 𝕋) :
    LinearSys.VerifyIterFloat 𝕋 :=
  let Rout := reachFn εmax                                                    -- 3. R̂(t)
  let Rin := innerApprox Rout εmax                                            -- 4. Ř(t), Sec. V
  let νGout := LinearSys.maximumFold fun j => distG Rout.conZonotope (G j) -- 5.-8. ν̂_G
  let νGin := LinearSys.maximumFold fun j => distG Rin (G j)           -- 5., 9.-10. ν̌_G
  let νFout := LinearSys.minimumFold fun j => distF Rout.conZonotope (F j) -- 5., 12.-14. ν̂_F
  let νFin := LinearSys.minimumFold fun j => distF Rin (F j)           -- 5., 12., 15.-16.
  let ν0 := minimum (neg νGin) νFin                                           -- 18.
  let ν1 := if le zero νGout then minimum ν0 νGout else ν0                    -- 19.-21.
  let ν2 := if le νFout zero then minimum ν1 (neg νFout) else ν1              -- 22.-24.
  let ten : 𝕋 := nsmulUp 10 one
  let εmax' := maximum (divDown εmax ten)                                     -- 25.
    (minimum ν2 (subDown εmax (divDown εmax ten)))
  { νGout := νGout, νGin := νGin, νFout := νFout, νFin := νFin, εmax := εmax' }

end


section
open FloatOps

@[step_of LinearSys.verifyFloat]
def LinearSys.step_verifyRunFloat (reachFn : 𝕋 → Zonotope (Vec 𝕋 n))
    (innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n))
    (distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (εmax : 𝕋) :
    ℕ → Option Bool
  | 0 => none
  | fuel + 1 =>
    let it :=
      LinearSys.step_verifyStepFloat reachFn innerApprox distG distF G F εmax      -- 3.-25.
    let verified := le it.νGout zero && ltStrict zero it.νFout                -- 27. (bνG≤0)∧(bνF>0)
    let falsified := ltStrict zero it.νGin || le it.νFin zero                 -- 26. (qνG>0)∨(qνF≤0)
    if verified || falsified then some verified                               -- 26. until, 27.
    else LinearSys.step_verifyRunFloat reachFn innerApprox distG distF G F it.εmax fuel -- 2. repeat

end


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: `true` where the specification is verified, `false` where it is falsified. -/
def LinearSys.verifyFloat (reachFn : 𝕋 → Zonotope (Vec 𝕋 n))
    (innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n))
    (distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋)
    (G : Fin (r + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (F : Fin (w + 1) → HPolytope 𝕋 (Vec 𝕋 n)) (εmax₀ : 𝕋)
    (fuel : ℕ) : Option Bool :=
  -- 1. ε_max ← ε_max₀
  LinearSys.step_verifyRunFloat reachFn innerApprox distG distF G F εmax₀ fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
