module

public import CORALean.ContDynamics.Conform.Definitions.State
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# A run splits into the nominal run and its deviation

The state from `x0 + x̃` under `u` and `w` is the nominal state from `x0` under `u`
plus `Aᵏ x̃ + ∑_{i<k} Aⁱ w(k-1-i)`, the deviation (22) names `x_a`: the model is
affine, and the deviation depends on neither `x0` nor `u`. Every statement that
subtracts the nominal run — [1, Eq. 15], [2, Eq. 8] — rests on this.

## Inputs
* `sys` – plant
* `x0` – nominal initial state
* `xt` – initial deviation
* `u` – inputs
* `w` – disturbances
* `k` – step

## Hypotheses
* none

## Conclusion
* the run is the nominal run plus the deviation

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
* [2] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The run from `x0 + x̃` is the nominal run from `x0` plus the deviation. -/
theorem Conform.Plant.state_add_dev (sys : Conform.Plant n p q) (x0 xt : Vec ℝ n)
    (u : ℕ → Vec ℝ p) (w : ℕ → Vec ℝ n) (k : ℕ) :
    sys.state (x0 + xt) u w k = sys.state x0 u 0 k
      + ((sys.A ^ k) *ᵥ xt + ∑ i : Fin k, (sys.A ^ (i : ℕ)) *ᵥ w (k - 1 - i)) := by -- --- PROOF ---
  induction k with
  | zero => simp [Conform.Plant.state]
  | succ k ih =>
    simp only [Conform.Plant.state, ih, Pi.zero_apply, add_zero, mulVec_add, mulVec_mulVec,
      mulVec_sum]
    -- the new disturbance is the `i = 0` term, the old ones move up one power
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mulVec, Fin.val_succ, pow_succ']
    have hidx : ∑ i : Fin k, (sys.A * sys.A ^ (i : ℕ)) *ᵥ w (k + 1 - 1 - ((i : ℕ) + 1))
        = ∑ i : Fin k, (sys.A * sys.A ^ (i : ℕ)) *ᵥ w (k - 1 - i) :=
      Finset.sum_congr rfl fun i _ => by rw [show k + 1 - 1 - ((i : ℕ) + 1) = k - 1 - i by omega]
    rw [hidx, show k + 1 - 1 - 0 = k by omega]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
