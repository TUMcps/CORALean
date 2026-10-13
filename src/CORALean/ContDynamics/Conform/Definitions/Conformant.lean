import CORALean.ContDynamics.Conform.Definitions.ReachOut

/-!
# Test cases, and reachset conformance tested on them

A test case [1, Def. 3] is a measured output sequence with the inputs and the initial
state it was recorded under. `Conformant` is [1, Def. 5]: every measurement up to `K`
lies in the reachable set of its own test case, started from the recorded initial
state shifted by the initial uncertainty `X̃₀` of [2, Sec. 3] (`{0}` in [1]). Several
executions of one test case [3, Def. 4] are several test cases with equal `x0` and `u`.

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
* [2] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
* [3] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {n p q : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Def. 3]: measured outputs, the inputs, and the initial state. -/
structure Conform.TestCase (n p q : ℕ) where
  y : ℕ → Vec ℝ q
  u : ℕ → Vec ℝ p
  x0 : Vec ℝ n

/-- [1, Def. 5]: every measurement up to `K` in its test case's reachable set. -/
def Conform.Plant.Conformant {M : Type} (sys : Conform.Plant n p q) (X0 W : Set (Vec ℝ n))
    (V : Set (Vec ℝ q)) (T : M → Conform.TestCase n p q) (K : ℕ) : Prop :=
  ∀ m, ∀ k ≤ K, (T m).y k ∈ sys.reachOut ({(T m).x0} + X0) (T m).u W V k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
