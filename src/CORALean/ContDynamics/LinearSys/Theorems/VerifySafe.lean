module

public import CORALean.ContDynamics.LinearSys.Operations.Verify
public import CORALean.ContDynamics.LinearSys.Theorems.VerifySpecOfVerifyRun

@[expose] public section

/-!
# [1, Alg. 3]: `verify` answering `true` is sound

Relative to what the passed-in functions promise (`VerifySound`): where `verify` returns
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verify_safe
    {Reach : Set (Vec ℝ n)} {reachFn : ℝ → Zonotope (Vec ℝ n)}
    {innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n)}
    {distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ} {le : ℝ → ℝ → Bool}
    (h : LinearSys.VerifySound Reach reachFn innerApprox distG distF le)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (εmax₀ : ℝ) (fuel : ℕ)
    (hv : LinearSys.verify reachFn innerApprox distG distF G F le εmax₀ fuel = some true)
    : -- --- CONCL ---
    LinearSys.VerifySpec G F Reach :=
  LinearSys.verifySpec_of_verifyRun h G F εmax₀ fuel hv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
