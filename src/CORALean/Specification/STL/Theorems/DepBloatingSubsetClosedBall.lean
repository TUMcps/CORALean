module

public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesSubsetClosedBall
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusSubsetClosedBall
public import CORALean.Specification.STL.Operations.DepBloating

@[expose] public section

/-!
# The bloating lies in an explicit ball

[1, Prop. 3], the bound behind the limit: for `U₀ ⊆ B_r(0)`, the three terms of `D` of
Eq. (15) lie in the balls of radius `‖Σ_{j≤κ} A^j Δt^{j+1}/(j+1)!‖ r`, `Σ_{j<κ} ‖A^{j+1}
Δt^{j+2}/(j+2)!‖ r` and `ρ Σ_j absBound_j(U₀)`, `ρ` the sum of the entries of `2Δt E` in magnitude,
so `D` lies in the ball of the sum (the sup norm of `Vec`, the operator norm of `Mat`).

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Minkowski sum of the first `κ` images stays in the sum of their balls. -/
theorem STL.aux_foldl_subset_closedBall (A : Mat ℝ n n) (U₀ : Zonotope (Vec ℝ n)) (Δt r : ℝ)
    (hU : U₀.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r) (κ : ℕ) :
    ((List.range κ).foldl
      (fun Z j => Z.plus (Zonotope.mtimes (MatExp.particularCoeff A Δt (j + 1)) U₀))
      (Zonotope.ofPoint 0)).construct
      ⊆ Metric.closedBall (0 : Vec ℝ n)
        (∑ j ∈ Finset.range κ, ‖MatExp.particularCoeff A Δt (j + 1)‖ * r) := by -- --- PROOF ---
  induction κ with
  | zero =>
    intro x hx
    have h0 : x = 0 := by
      obtain ⟨β, -, hβ⟩ := Zonotope.mem_construct_iff.mp hx
      funext i; simpa [Zonotope.ofPoint] using hβ i
    simp [h0]
  | succ κ ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
    exact Zonotope.plus_subset_closedBall ih (Zonotope.mtimes_subset_closedBall _ hU)


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.depBloating_subset_closedBall (A : Mat ℝ n n) (U₀ : Zonotope (Vec ℝ n)) (Δt : ℝ)
    (κ : ℕ) {r : ℝ} (hU : U₀.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r) :
    (STL.depBloating A U₀ Δt κ).construct ⊆ Metric.closedBall (0 : Vec ℝ n)
      (‖∑ j ∈ Finset.Icc 1 κ, MatExp.particularCoeff A Δt j‖ * r
        + ∑ j ∈ Finset.range κ, ‖MatExp.particularCoeff A Δt (j + 1)‖ * r
        + (∑ i, ∑ j, |(2 * Δt) * MatExp.expRemainderMat A Δt κ i j|)
          * ∑ j, U₀.absBound j) := by -- --- PROOF ---
  have h1 := Zonotope.mtimes_subset_closedBall (∑ j ∈ Finset.Icc 1 κ, MatExp.particularCoeff A Δt j)
    hU
  have h2 := STL.aux_foldl_subset_closedBall A U₀ Δt r hU κ
  have hρ : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, |(2 * Δt) * MatExp.expRemainderMat A Δt κ i j| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- the third term, `2Δt E U₀`: the interval matrix has centre `0` and radius `2Δt E`
  have h3 := Zonotope.mtimesIntervalMat_subset_closedBall
    (⟨-((2 * Δt) • MatExp.expRemainderMat A Δt κ), (2 * Δt) • MatExp.expRemainderMat A Δt κ⟩ :
      Interval (Mat ℝ n n)) U₀ (le_refl 0) hρ
    (fun i j => by simp [Interval.center])
    (fun i j => by
      have h : (2:ℝ)⁻¹ • ((2 * Δt) • MatExp.expRemainderMat A Δt κ
          - -((2 * Δt) • MatExp.expRemainderMat A Δt κ)) =
          (2 * Δt) • MatExp.expRemainderMat A Δt κ := by
        rw [sub_neg_eq_add, ← two_smul ℝ, smul_smul]; norm_num
      show |((2:ℝ)⁻¹ • ((2 * Δt) • MatExp.expRemainderMat A Δt κ
          - -((2 * Δt) • MatExp.expRemainderMat A Δt κ))) i j| ≤ _
      rw [h]
      refine (Finset.single_le_sum (f := fun j => |(2 * Δt) * MatExp.expRemainderMat A Δt κ i j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans ?_
      exact Finset.single_le_sum (f := fun i => ∑ j, |(2 * Δt) * MatExp.expRemainderMat A Δt κ i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  rw [zero_add] at h3
  exact Zonotope.plus_subset_closedBall
    (Zonotope.plus_subset_closedBall h1 h2) h3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
