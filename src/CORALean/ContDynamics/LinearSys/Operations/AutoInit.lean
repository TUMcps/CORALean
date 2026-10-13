module

public import CORALean.ContDynamics.LinearSys.Definitions.AutoState

@[expose] public section

/-!
# `Alg. 2` lines 1-2: the loop state before the first iteration

`autoInit`: [1, Alg. 2] lines 1-2, before the first iteration.

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
noncomputable def LinearSys.autoInit (X₀ : Zonotope (Vec ℝ n)) (tend : ℝ) :
    LinearSys.AutoState n :=
  { t := 0                          -- 1. t₀ ← 0
    Δt := tend                      -- 1. Δt₋₁ ← t_end
    H := X₀                         -- 1. H(t₀) ← X₀
    Pu := 0                         -- 2. P^u(t₀) ← ⟨0,[]⟩_Z
    PU0 := Zonotope.ofPoint 0       -- 2. P̂^U_0(t₀) ← ⟨0,[]⟩_Z
    PUinf := Zonotope.ofPoint 0     -- 2. P̂^U_∞(t₀) ← ⟨0,[]⟩_Z
    εa := 0
    εr := 0 }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
