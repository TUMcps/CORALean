module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulLe
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesSubsetClosedBall
public import CORALean.Specification.STL.Operations.DepReachAt

@[expose] public section

/-!
# The curvature set at the `i`-th step lies in a ball independent of `i`

[1, Prop. 4]: `C_{i+1} = e^{AΔt} C_i` (line 5 of Alg. 1) multiplies the reach of the ball by
`‖e^{AΔt}‖ ≤ e^{Δt‖A‖}` per step, so `C_i ⊆ B_{ρ e^{iΔt‖A‖}}(0)` if `C₀ ⊆ B_ρ(0)`, and for
`iΔt ≤ T` the radius is at most `e^{T‖A‖} ρ`: the bound the printed proof of Prop. 4 does not give
(it lets `Δt → 0` at a fixed `i`, where `iΔt = t_i` also moves).

## Inputs
* `A` – dynamics matrix
* `Δt` – time step
* `cs` – constants of the algorithm
* `X₀` – initial set
* `ρ` – initial ball radius
* `T` – final time
* `i` – step index

## Hypotheses
* `hΔt` – the time step is nonnegative
* `hρ` – the radius is nonnegative
* `h0` – the initial curvature set lies in the ball
* `hi` – the step time is within the final time

## Conclusion
* the curvature set lies in a ball independent of the step

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.depReachAt_C_subset_closedBall (A : Mat ℝ n n) {Δt : ℝ} (hΔt : 0 ≤ Δt)
    (cs : STL.DepReachConsts n) (X₀ : Zonotope (Vec ℝ n)) {ρ T : ℝ} (hρ : 0 ≤ ρ)
    (h0 : (STL.depReachAt A Δt cs X₀ 0).C.construct ⊆ Metric.closedBall (0 : Vec ℝ n) ρ)
    (i : ℕ) (hi : (i : ℝ) * Δt ≤ T) : -- --- CONCL ---
    (STL.depReachAt A Δt cs X₀ i).C.construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) (Real.exp (T * ‖A‖) * ρ) := by -- --- PROOF ---
  have hstep : ∀ i, (STL.depReachAt A Δt cs X₀ i).C.construct
      ⊆ Metric.closedBall (0 : Vec ℝ n) (‖exp (Δt • A)‖ ^ i * ρ) := by
    intro i
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      have := Zonotope.mtimes_subset_closedBall (exp (Δt • A)) ih
      rw [pow_succ, mul_comm (‖exp (Δt • A)‖ ^ i) ‖exp (Δt • A)‖, mul_assoc]
      exact this
  refine (hstep i).trans (Metric.closedBall_subset_closedBall ?_)
  have h1 : ‖exp (Δt • A)‖ ^ i ≤ Real.exp (T * ‖A‖) := by
    calc ‖exp (Δt • A)‖ ^ i ≤ Real.exp (Δt * ‖A‖) ^ i :=
          pow_le_pow_left₀ (norm_nonneg _) (MatExp.norm_exp_smul_le A hΔt) i
      _ = Real.exp (i * (Δt * ‖A‖)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (T * ‖A‖) := by
          refine Real.exp_le_exp.mpr ?_
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)
  exact mul_le_mul_of_nonneg_right h1 hρ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
