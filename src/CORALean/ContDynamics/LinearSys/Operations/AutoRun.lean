import CORALean.ContDynamics.LinearSys.Operations.AutoInit
import CORALean.ContDynamics.LinearSys.Operations.AutoStep

/-!
# `Alg. 2` lines 4-31: the loop

`autoRun`: [1, Alg. 2] lines 4-31, iterate `autoStep` while `t_k < t_end`, `none` propagating
once the tuning has given out at some step.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-31: iterate `autoStep` while `t_k < t_end`, `none` propagating once the tuning
has given out at some step. -/
noncomputable def LinearSys.autoRun (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (tend εmax ζ : ℝ) (ηmax fuel : ℕ) :
    ℕ → Option (LinearSys.AutoState n)
  | 0 => some (LinearSys.autoInit X₀ tend)                             -- 1.-3. initialize
  | k + 1 =>
    match sys.autoRun le X₀ U tend εmax ζ ηmax fuel k with
    | none => none
    | some s =>
      if s.t < tend                                                   -- 4. while t_k < t_end
      then (sys.autoStep le X₀ U tend εmax ζ ηmax fuel s).map Prod.fst
      else some s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
