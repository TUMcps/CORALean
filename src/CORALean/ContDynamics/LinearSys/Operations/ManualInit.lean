import CORALean.ContDynamics.LinearSys.Definitions.ManualState

/-!
# `Alg. 1` lines 1-2: the loop state before the first iteration

`manualInit`: [1, Alg. 1] lines 1-2, before the first iteration.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 1-2, before the first iteration. -/
noncomputable def LinearSys.manualInit (X₀ : Zonotope (Vec ℝ n)) : LinearSys.ManualState n :=
  { t := 0                          -- 1. t₀ ← 0
    H := X₀                         -- 2. H(t₀) ← X₀
    Pu := 0                         -- 2. P^u(t₀) ← 0
    PU := Zonotope.ofPoint 0 }      -- 2. P̂^U(t₀) ← 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
