import CORALean.HybridDynamics.Operations.SdcFlow
import CORALean.HybridDynamics.Definitions.SdcInput
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
import Mathlib.Topology.Instances.Matrix

/-!
# [1, Prop. 1]: the state difference vanishes as the order grows

At `b = Θ(t̃_h)x₀ + Γ*(t̃_h)u_c`, the flow `y(t̃_h) = x₀ + (Ax₀ + b)t̃_h` is the Taylor
polynomial of order `η` of the linear system's solution `x(t̃_h) = e^{At̃_h}x₀ + Γ(t̃_h)u_c`,
eq. (5): `x₀ + Ax₀t + tΘ(t)x₀` is `Σᵢ₌₀^η (At)ⁱ/i! x₀` once `η ≥ 1`, and `tΓ*(t)` is
`Σᵢ₌₀^η Aⁱtⁱ⁺¹/(i + 1)!`, so the error `e(t̃_h) = x(t̃_h) - y(t̃_h)` is the two series' tails,
which vanish — the proof's `Ê(t̃_h)x₀ ⊕ Ê(t̃_h)t̃_h u_c` at `ξ = x₀`.

That is the content of the proposition, which also says `b` "minimizes" the error; at a
fixed `η` it does not, see the page's `## Findings`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- From `η = 1` on, the flow at `t` is the two truncated series applied. -/
theorem GuardMap.aux_sdcFlow_eq (A : Mat ℝ n n) (x₀ uc : Vec ℝ n) (t : ℝ) {η : ℕ} (hη : 1 ≤ η) :
    GuardMap.sdcFlow A (GuardMap.sdcInput A uc t η x₀) x₀ t
      = (∑ i ∈ Finset.range (η + 1), (((i.factorial : ℝ))⁻¹ * t ^ i) • A ^ i) *ᵥ x₀
        + (∑ i ∈ Finset.range (η + 1),
            ((((i + 1).factorial : ℝ))⁻¹ * t ^ (i + 1)) • A ^ i) *ᵥ uc := by -- --- PROOF ---
  obtain ⟨k, rfl⟩ : ∃ k, η = k + 1 := ⟨η - 1, by omega⟩
  -- `tΓ*(t)` is the integrated series, term by term
  have hP : t • ∑ i ∈ Finset.range (k + 1 + 1), (t ^ i / ((i + 1).factorial : ℝ)) • A ^ i
      = ∑ i ∈ Finset.range (k + 1 + 1), ((((i + 1).factorial : ℝ))⁻¹ * t ^ (i + 1)) • A ^ i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    rw [pow_succ]
    ring
  -- `I + tA + tΘ(t)` is the exponential series to order `k + 1`
  have hS : ∑ i ∈ Finset.range (k + 1 + 1), (((i.factorial : ℝ))⁻¹ * t ^ i) • A ^ i
      = 1 + t • A + t • ∑ i ∈ Finset.Ico 2 (k + 1 + 1),
          (t ^ (i - 1) / (i.factorial : ℝ)) • A ^ i := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_Ico_eq_sum_range,
      Finset.smul_sum, show k + 1 + 1 - 2 = k by omega]
    simp only [pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
      one_mul, mul_one, one_smul, zero_add]
    rw [add_comm (_ + _) (1 : Mat ℝ n n), add_comm (∑ i ∈ Finset.range k, _) (t • A), ← add_assoc]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, show 2 + i - 1 = i + 1 by omega, add_comm 2 i]
    congr 1
    rw [pow_succ]
    ring
  simp only [GuardMap.sdcFlow, GuardMap.sdcInput]
  rw [hS, ← hP]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, smul_add]
  abel


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: `e(t̃_h) = x(t̃_h) - y(t̃_h) → 0` as `η → ∞`. -/
theorem GuardMap.tendsto_sdcFlow_error (A : Mat ℝ n n) (x₀ uc : Vec ℝ n) (t : ℝ) :
    Tendsto (fun η : ℕ => (exp (t • A) *ᵥ x₀ + Real.MatExp.expIntegral A t *ᵥ uc)
        - GuardMap.sdcFlow A (GuardMap.sdcInput A uc t η x₀) x₀ t)
      atTop (𝓝 0) := by -- --- PROOF ---
  -- the two series, summed to order `η`
  have hS := ((Real.summable_exp_smul A t).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  rw [← Real.exp_smul_tsum] at hS
  have hP : Tendsto ((fun k => ∑ i ∈ Finset.range k,
      ((((i + 1).factorial : ℝ))⁻¹ * t ^ (i + 1)) • A ^ i) ∘ fun a => a + 1) atTop
      (𝓝 (Real.MatExp.expIntegral A t)) :=
    ((Real.MatExp.summable_expIntegral A t).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hcont : ∀ v : Vec ℝ n, Continuous fun M : Mat ℝ n n => M *ᵥ v := fun v =>
    continuous_id.matrix_mulVec continuous_const
  have hlim := ((hcont x₀).tendsto _).comp hS |>.add (((hcont uc).tendsto _).comp hP)
  have h0 := (tendsto_const_nhds
    (x := exp (t • A) *ᵥ x₀ + Real.MatExp.expIntegral A t *ᵥ uc)).sub hlim
  rw [sub_self] at h0
  refine h0.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with η hη
  simp only [Function.comp_apply]
  rw [GuardMap.aux_sdcFlow_eq A x₀ uc t hη]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
