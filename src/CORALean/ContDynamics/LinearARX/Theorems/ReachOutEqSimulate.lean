import CORALean.ContDynamics.LinearARX.Definitions.ReachOut
import CORALean.ContDynamics.LinearARX.Theorems.EqSimulate
import CORALean.ContDynamics.LinearARX.Theorems.StackSimulateZero

/-!
# Exact addition is exact

[1, Prop. 3]: evaluating the recursion (6) with exact addition `⊞` — every set a function
of one shared input signal `λ`, the generating functions summed pointwise — gives `Y(k)`
exactly. That evaluation, at the signal `u`, is `simulate y₀ u k`; so `Y(k)` is the image
of the admissible signals under it, by `eq_simulate` one way and `simulate` the other.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.reachOut_eq_simulate (sys : LinearARX 𝕋 dy du p) (y₀ : Vec ℝ (p * dy))
    (U : ℕ → Set (Vec ℝ du)) (k : ℕ) :
    sys.reachOut y₀ U k
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
