module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyIter
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContDynamics.LinearSys.Operations.VerifyRun
public import CORALean.ContDynamics.LinearSys.Operations.VerifyStep

@[expose] public section

/-!
# `Alg. 3` line 1: automated verification

`verify`: `true` where the specification given by the safe sets `G` and unsafe sets `F` is
verified, `false` where it is falsified, `none` where `fuel` repeat-until iterations did not
reach a verdict. Line 1's "estimated from simulations" is left a parameter, `ε_max₀`.

## Inputs
* `reachFn` – reachable set as a function of the error
* `innerApprox` – inner approximation at an error
* `distG` – distance to a safe polytope
* `distF` – distance to an unsafe polytope
* `G` – safe polytopes
* `F` – unsafe polytopes
* `le` – comparison oracle on reals
* `εmax₀` – initial maximal error
* `fuel` – number of iterations

## Output
* verdict: verified, falsified, or undecided

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n r w : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: `true` where the specification given by the safe sets `G` and unsafe sets `F`
is verified, `false` where it is falsified, `none` where `fuel` repeat-until iterations did not
reach a verdict. -/
noncomputable def LinearSys.verify (reachFn : ℝ → Zonotope (Vec ℝ n))
    (innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n))
    (distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (le : ℝ → ℝ → Bool) (εmax₀ : ℝ) (fuel : ℕ) : Option Bool :=
  -- 1. ε_max ← ε_max₀
  LinearSys.verifyRun reachFn innerApprox distG distF G F le εmax₀ fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
