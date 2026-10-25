module

public import CORALean.ContDynamics.LinearARX.Definitions.ReachOutExact
public import CORALean.ContDynamics.LinearARX.Theorems.EqSimulate
public import CORALean.ContDynamics.LinearARX.Theorems.StackSimulateZero

@[expose] public section

/-!
# Exact addition is exact

[1, Prop. 3]: evaluating the recursion (6) with exact addition `⊞` — every set a function
of one shared input signal `λ`, the generating functions summed pointwise — gives `Y(k)`
exactly. That evaluation, at the signal `u`, is `simulate y₀ u k`; so `Y(k)` is the image
of the admissible signals under it, by `eq_simulate` one way and `simulate` the other.

## Inputs
* `sys` – ARX system
* `y₀` – measured first output window
* `U` – input sets per step
* `k` – step

## Hypotheses
* none

## Conclusion
* the reachable outputs are the simulations over all admissible inputs

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.reachOutExact_eq_simulate (sys : LinearARX 𝕋 dy du p) (y₀ : Vec ℝ (p * dy))
    (U : ℕ → Set (Vec ℝ du)) (k : ℕ) : -- --- CONCL ---
    sys.reachOutExact y₀ U k
      = (fun u => sys.simulate y₀ u k) '' {u | ∀ i, u i ∈ U i} := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨y, u, h₀, hu, hy, rfl⟩
    exact ⟨u, hu, (sys.eq_simulate h₀ hy k).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨sys.simulate y₀ u, u, sys.stack_simulate_zero y₀ u, hu, fun k hk => ?_, rfl⟩
    rw [LinearARX.simulate, dif_neg (not_lt.mpr hk)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
