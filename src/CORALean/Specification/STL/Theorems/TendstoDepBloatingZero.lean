module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderMatZero
public import CORALean.ContSet.Zonotope.Real.Theorems.SubsetClosedBallOfAbsBoundLe
public import CORALean.Specification.STL.Operations.DepReachConstsOf
public import CORALean.Specification.STL.Theorems.DepBloatingSubsetClosedBall
public import CORALean.Specification.STL.Theorems.TendstoSSupNormOfEventuallySubsetClosedBall

@[expose] public section

/-!
# [1, Prop. 3]: the bloating vanishes with the step

`lim_{Δt→0} 𝒟 = 0` for the bloating `𝒟` of Eq. (15), at the order `κ` fixed: `D` lies in the sup
norm ball of radius `‖Σ_{j≤κ} A^j Δt^{j+1}/(j+1)!‖ r + Σ_{j<κ} ‖A^{j+1} Δt^{j+2}/(j+2)!‖ r +
ρ(Δt) Σ_j absBound_j(U₀)` (`STL.depBloating_subset_closedBall`) and each of the three terms tends to
`0`, the matrix coefficients by continuity at `Δt = 0` where `Δt^{j+1} = 0`, `ρ` (the entries of
`2Δt E`) because `E → 0` (`MatExp.tendsto_expRemainderMat_zero`). "`→ 0`" is the radius
`sup_{v ∈ 𝒟} ‖v‖` of the set in the sup norm of `Vec`, along `Δt → 0⁺`.

## Inputs
* `A` – dynamics matrix
* `B` – input matrix
* `U` – input set
* `κ` – Taylor order

## Hypotheses
* none

## Conclusion
* the bloating shrinks to zero with the step

## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.tendsto_depBloating_zero (A : Mat ℝ n n) (B : Mat ℝ n m) (U : Zonotope (Vec ℝ m))
    (κ : ℕ) : -- --- CONCL ---
    Tendsto (fun Δt : ℝ =>
      sSup ((fun v => ‖v‖) '' (STL.depReachConsts A B U Δt κ).D.construct))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by -- --- PROOF ---
  set U₀ : Zonotope (Vec ℝ n) := Zonotope.mtimes B (U.plus (Zonotope.ofPoint (-U.c))) with hU₀
  set r : ℝ := ∑ j, U₀.absBound j with hr
  have habs : ∀ j, 0 ≤ U₀.absBound j := fun j =>
    add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun j _ => habs j
  have hball : U₀.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r :=
    Zonotope.subset_closedBall_of_absBound_le hr0 fun j =>
      Finset.single_le_sum (f := fun j => U₀.absBound j) (fun j _ => habs j) (Finset.mem_univ j)
  -- the coefficient matrices vanish with the step
  have hpc : ∀ j : ℕ, Tendsto (fun Δt : ℝ => ‖MatExp.particularCoeff A Δt j‖) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
    intro j
    have hc : Continuous fun Δt : ℝ => MatExp.particularCoeff A Δt j := by
      unfold MatExp.particularCoeff
      fun_prop
    have h0 := ((hc.tendsto 0).norm).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [MatExp.particularCoeff] using h0
  -- the sum of the coefficients, the first term of `D`
  have hsum : Tendsto (fun Δt : ℝ => ‖∑ j ∈ Finset.Icc 1 κ, MatExp.particularCoeff A Δt j‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun Δt : ℝ => ∑ j ∈ Finset.Icc 1 κ, MatExp.particularCoeff A Δt j := by
      refine continuous_finsetSum _ fun j _ => ?_
      unfold MatExp.particularCoeff
      fun_prop
    have h0 := ((hc.tendsto 0).norm).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [MatExp.particularCoeff] using h0
  -- the entries of `2Δt E`
  have hE : ∀ i j : Fin n, Tendsto (fun Δt : ℝ =>
      |(2 * Δt) * MatExp.expRemainderMat A Δt κ i j|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro i j
    have h1 : Tendsto (fun Δt : ℝ => MatExp.expRemainderMat A Δt κ i j) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (MatExp.tendsto_expRemainderMat_zero A κ) i) j
    have h2 : Tendsto (fun Δt : ℝ => 2 * Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun Δt : ℝ => Δt)
        (𝓝[>] (0 : ℝ)) (𝓝 0)).const_mul 2
    simpa using (h2.mul h1).abs
  have hρ : Tendsto (fun Δt : ℝ => ∑ i : Fin n, ∑ j : Fin n,
      |(2 * Δt) * MatExp.expRemainderMat A Δt κ i j|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => hE i j
  -- the three terms of the radius vanish together
  have hbound : Tendsto (fun Δt : ℝ =>
      ‖∑ j ∈ Finset.Icc 1 κ, MatExp.particularCoeff A Δt j‖ * r
        + ∑ j ∈ Finset.range κ, ‖MatExp.particularCoeff A Δt (j + 1)‖ * r
        + (∑ i : Fin n, ∑ j : Fin n, |(2 * Δt) * MatExp.expRemainderMat A Δt κ i j|)
          * ∑ j, U₀.absBound j) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h2 := tendsto_finsetSum (Finset.range κ) fun j _ => (hpc (j + 1)).mul_const r
    simpa using ((hsum.mul_const r).add h2).add (hρ.mul_const (∑ j, U₀.absBound j))
  refine STL.tendsto_sSup_norm_of_eventually_subset_closedBall fun ε hε => ?_
  filter_upwards [hbound.eventually (gt_mem_nhds hε)] with Δt hΔt
  exact (STL.depBloating_subset_closedBall A U₀ Δt κ hball).trans
    (Metric.closedBall_subset_closedBall hΔt.le)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
