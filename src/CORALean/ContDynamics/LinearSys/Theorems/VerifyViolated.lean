import CORALean.ContDynamics.LinearSys.Operations.Verify
import CORALean.ContDynamics.LinearSys.Theorems.NotVerifySpecOfVerifyRun

/-!
# [1, Alg. 3]: `verify` answering `false` is sound

Relative to what the passed-in functions promise (`VerifySound`): where `verify` returns
`some false`, some trajectory reaches a state outside a safe set or inside an unsafe one.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n r w : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verify_violated
    {Reach : Set (Vec ℝ n)} {reachFn : ℝ → Zonotope (Vec ℝ n)}
    {innerApprox : Zonotope (Vec ℝ n) → ℝ → ConZonotope (Vec ℝ n)}
    {distG distF : ConZonotope (Vec ℝ n) → HPolytope (Vec ℝ n) → ℝ} {le : ℝ → ℝ → Bool}
    (h : LinearSys.VerifySound Reach reachFn innerApprox distG distF le)
    (G : Fin (r + 1) → HPolytope (Vec ℝ n)) (F : Fin (w + 1) → HPolytope (Vec ℝ n))
    (εmax₀ : ℝ) (fuel : ℕ)
    (hv : LinearSys.verify reachFn innerApprox distG distF G F le εmax₀ fuel = some false) :
    ¬ LinearSys.VerifySpec G F Reach :=
  LinearSys.not_verifySpec_of_verifyRun h G F εmax₀ fuel hv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
