module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The model a reachset-conformance test is about

`x(k+1) = A x(k) + B u(k) + w(k)`, `y(k) = C x(k) + D u(k) + v(k)` [1, Eq. 5], over ℝ: the
discrete-time model of [2, Sec. 3] and the state-space model of [3, Cor. 1] with linear `f`, `g`.
Kept apart from `LinearSysDT`, which folds `B u` into its input: conformance subtracts the run
under the *known* inputs `u` from the measurements and keeps `w` and `v` as the unknowns. Every
object here is a specification over ℝ and nothing is computed, so there is no scalar parameter
and no float layer: CORA hands its programs to a solver (`linprog`, `quadprog`).

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


-- ========================================  MAIN TYPE  ========================================= --

/-- [1, Eq. 5]'s matrices: `n` states, `p` inputs, `q` outputs. -/
structure Conform.Plant (n p q : ℕ) where
  A : Mat ℝ n n
  B : Mat ℝ n p
  C : Mat ℝ q n
  D : Mat ℝ q p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
