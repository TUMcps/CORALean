module

public import CORALean.ContDynamics.Conform.Definitions.State
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# The reachable sets of the model, exactly

`reachState X0 u W k` is every state `k` steps of [1, Eq. 5] reach from `X0` under the
known inputs `u`, the disturbance free in `W` at each step; `reachOut` adds the output
map and the noise `V`. These are [1, Def. 5]'s `R(k)` and [2, Eq. 3]'s `R(t_k)` read
for the discrete-time model, and what every conformance statement here is about.

Only `w(0), …, w(k-1)` constrain the set at `k`, so only they are required to lie
in `W`; no nonemptiness of `W` is then needed for the steps past `k`.

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

variable {n p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in exactly `k` steps. -/
def Conform.Plant.reachState (sys : Conform.Plant n p q) (X0 : Set (Vec ℝ n))
    (u : ℕ → Vec ℝ p) (W : Set (Vec ℝ n)) (k : ℕ) : Set (Vec ℝ n) :=
  {x | ∃ x0 ∈ X0, ∃ w : ℕ → Vec ℝ n, (∀ i < k, w i ∈ W) ∧ x = sys.state x0 u w k}

/-- [1, Def. 5]'s reachable output set at `k`. -/
def Conform.Plant.reachOut (sys : Conform.Plant n p q) (X0 : Set (Vec ℝ n))
    (u : ℕ → Vec ℝ p) (W : Set (Vec ℝ n)) (V : Set (Vec ℝ q)) (k : ℕ) : Set (Vec ℝ q) :=
  {y | ∃ x0 ∈ X0, ∃ w : ℕ → Vec ℝ n, (∀ i < k, w i ∈ W) ∧
    ∃ v ∈ V, y = sys.output x0 u w k + v}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
