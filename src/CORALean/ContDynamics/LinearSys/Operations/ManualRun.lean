module

public import CORALean.ContDynamics.LinearSys.Definitions.ManualState
public import CORALean.ContDynamics.LinearSys.Operations.ManualStep

@[expose] public section

/-!
# `Alg. 1` lines 4-11: the loop

`manualRun`: [1, Alg. 1] lines 4-11, iterate `manualStep` `k` times, reaching the state at
`t_k`.

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

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lines 1-2, before the first iteration. -/
noncomputable def LinearSys.aux_manualInit (X₀ : Zonotope (Vec ℝ n)) : LinearSys.ManualState n :=
  { t := 0                          -- 1. t₀ ← 0
    H := X₀                         -- 2. H(t₀) ← X₀
    Pu := 0                         -- 2. P^u(t₀) ← 0
    PU := Zonotope.ofPoint 0 }      -- 2. P̂^U(t₀) ← 0


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-11: iterate `manualStep` `k` times, reaching the state at `t_k`. -/
noncomputable def LinearSys.manualRun (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec ℝ n))
    (Δt : ℝ) (η ρ : ℕ) : ℕ → LinearSys.ManualState n
  | 0 => LinearSys.aux_manualInit X₀
  | k + 1 => (sys.manualStep X₀ U Δt η ρ (sys.manualRun X₀ U Δt η ρ k)).1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
