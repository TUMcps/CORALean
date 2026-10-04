import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# The model a reachset-conformance test is about

`x(k+1) = A x(k) + B u(k) + w(k)`, `y(k) = C x(k) + D u(k) + v(k)` [1, Eq. 5], over ℝ:
the discrete-time model of [2, Sec. 3] and the state-space model of [3, Cor. 1] with
linear `f`, `g`.
Kept apart from `LinearSysDT`, which folds `B u` into its input: conformance subtracts
the run under the *known* inputs `u` from the measurements and keeps the disturbance
`w` and the noise `v` as the unknowns, so the two must not be one signal.

Every object here is a specification over ℝ — a set of outputs, a linear program's
feasible set — and nothing is computed, so there is no scalar parameter and no float
layer: the programs are handed to a solver in CORA (`linprog`, `quadprog`), and what
is proved is what any feasible point of them guarantees.

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

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Eq. 5]'s matrices: `n` states, `p` inputs, `q` outputs. -/
structure Conform.Plant (n p q : ℕ) where
  A : Mat ℝ n n
  B : Mat ℝ n p
  C : Mat ℝ q n
  D : Mat ℝ q p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
