module

public import CORALean.ContDynamics.LinearSys.Definitions.HeldSim

@[expose] public section

/-!
# The discrete-time system in closed form

[1, Sec. 4.2]'s recursion, unrolled: `x(k)` is `e^{AΔt k} x₀` plus every input
carried from its step to `t_k`, `u(i)` by `e^{AΔt (k-1-i)} T`. Which direction
each input has to maximize, for `x(k)` to be a support vector, is read off here.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `x₀` – initial state
* `u` – input value per step
* `k` – step index

## Hypotheses
* none

## Conclusion
* the discrete-time state has the closed form

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]'s Eq. (18) in closed form:
`x(k) = e^{AΔt k} x₀ + ∑_{i<k} e^{AΔt (k-1-i)} T u(i)`. -/
theorem LinearSys.heldSim_eq (sys : LinearSys 𝕋 n) (Δt : ℝ) (x₀ : Vec ℝ n) (u : ℕ → Vec ℝ n)
    (k : ℕ) : -- --- CONCL ---
    sys.heldSim Δt x₀ u k
      = exp (Δt • toRealMat sys.A) ^ k *ᵥ x₀
        + ∑ i ∈ Finset.range k, exp (Δt • toRealMat sys.A) ^ (k - 1 - i) *ᵥ
            (MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ u i) := by -- --- PROOF ---
  induction k with
  | zero => simp [LinearSys.heldSim]
  | succ k ih =>
    show exp (Δt • toRealMat sys.A) *ᵥ sys.heldSim Δt x₀ u k
      + MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ u k = _
    rw [ih, mulVec_add, mulVec_mulVec, ← pow_succ', Finset.sum_range_succ, Matrix.mulVec_sum,
      Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mulVec, add_assoc]
    congr 2
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mulVec_mulVec, ← pow_succ']
    congr 2
    have := Finset.mem_range.mp hi
    omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
