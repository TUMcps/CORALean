module

public import CORALean.ContDynamics.Conform.Plant

@[expose] public section

/-!
# One run of the model, and its outputs

The state after `k` steps of [1, Eq. 5] from `x0`, under inputs `u` and disturbances
`w`; the output at `k` adds `D u(k)` and the noise. `nominal` is the run without
disturbance and noise, [1, Eq. 14]'s `y_*` and [2, Sec. 3]'s `ỹ`: what a measurement is
compared against once the test case's initial state and inputs are put in.

## Inputs
* `sys` – plant
* `x0` – initial state
* `u` – inputs
* `w` – disturbances

## Output
* the state after each number of steps

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems: Unifying Formal
      Controller Synthesis and Reachset-Conformant Identification". IEEE Transactions on Robotics,
      2023.
* [2] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". Proceedings of 10th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH23),
      2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The state after `k` steps of [1, Eq. 5]. -/
noncomputable def Conform.Plant.state (sys : Conform.Plant n p q) (x0 : Vec ℝ n)
    (u : ℕ → Vec ℝ p) (w : ℕ → Vec ℝ n) : ℕ → Vec ℝ n
  | 0 => x0
  | k + 1 => sys.A *ᵥ sys.state x0 u w k + sys.B *ᵥ u k + w k

/-- The run's output at `k`, before the noise `v(k)` is added. -/
noncomputable def Conform.Plant.output (sys : Conform.Plant n p q) (x0 : Vec ℝ n)
    (u : ℕ → Vec ℝ p) (w : ℕ → Vec ℝ n) (k : ℕ) : Vec ℝ q :=
  sys.C *ᵥ sys.state x0 u w k + sys.D *ᵥ u k

/-- [1, Eq. 14]'s nominal output `y_*`: no disturbance, no noise. -/
noncomputable def Conform.Plant.nominal (sys : Conform.Plant n p q) (x0 : Vec ℝ n)
    (u : ℕ → Vec ℝ p) (k : ℕ) : Vec ℝ q :=
  sys.output x0 u 0 k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
