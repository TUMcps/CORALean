import CORALean.ContDynamics.LinearSys.LinearSys
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed

/-!
# A one-step particular solution, propagated over a horizon

The recursion [1, Prop. 1] propagates its two approximations by: the set reached
so far, plus what one more step contributes, carried across the elapsed time by
`e^{A t_k}` rather than the accumulated set being mapped — which is what keeps
the wrapping effect out.

Taken at an arbitrary one-step set, so the outer approximation, the inner
approximation and the exact particular solution are the same recursion at three
arguments, and the proofs about it are shared.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Z_S(t_k)` after `k` steps of length `Δt`, from the one-step set `Z`. -/
noncomputable def LinearSys.propagateInputSolution (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (Z : Set (Vec ℝ n)) : ℕ → Set (Vec ℝ n)
  | 0 => {0}
  | k + 1 => sys.propagateInputSolution Δt Z k
      + (fun y => exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ y) '' Z

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
