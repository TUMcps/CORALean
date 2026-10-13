import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalMulVecSet
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff

/-!
# `bPU`, eq. (20): the particular solution's outer-approximation

`particularSolutionOuter`: [1]'s `bPU(Δt,η) = ⊕ᵢ₌₀^η ÃᵢU0 ⊕ E(Δt,η)ΔtU0` (eq. 20), read as a
`Set`: `⊕` is Minkowski sum, and `E(Δt,η)ΔtU0` is every `M.mulVec` image of `ΔtU0` for `M`
entrywise within `|E(Δt,η)|` of `0` — the standard reading of an interval matrix acting on a
vector set. `i0` starts the sum at `0` for `bPU` itself or at `1` for `bPU_∞` of eq. (27),
which [1, Lemma 2]'s second `err` term and [1, Lemma 4] both need.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s eq. (20): the particular solution's outer-approximation over one step, summed from
index `i0` (`0` for `bPU`, `1` for `bPU_∞` of eq. (27)) to the truncation order `η`. -/
noncomputable def MatExp.particularSolutionOuter (A : Mat ℝ n n) (U0 : Set (Vec ℝ n)) (i0 : ℕ)
    (Δt : ℝ) (η : ℕ) : Set (Vec ℝ n) :=
  (∑ i ∈ Finset.Ico i0 (η + 1), (fun x => (MatExp.particularCoeff A Δt i).mulVec x) '' U0) +
    MatExp.intervalMulVecSet (MatExp.expRemainderMat A Δt η) (Δt • U0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
