import CORALean.ContDynamics.LinearSys.Theorems.GirardExampleSpec
import CORALean.ContDynamics.LinearSys.Theorems.GirardReachEq

/-!
# [1, Thm. 1]'s convergence bound, as printed, is false

[1, Thm. 1] states `d_H(R_[0,T](I), R_{N-1}) ≤ r‖A‖e^{‖A‖T}(2µ/‖A‖ + (1/2 + r) sup ‖x‖)`.
At `N = 1`, `T = r`, [1, Alg. 1] returns `R₀ = Q₀`, the set of [1, Lemma 2], and with `µ = 0`
the two bounds agree; so `girardExample_spec`, which breaks [1, Lemma 2], breaks this too:
`x' = 100x`, `I = [0, 2]`, `r = 1/100`, bound `1.02e ≈ 2.77`, distance at least `3e - 5 ≈ 3.15`.
`sup_{x∈Z}` in the printed statement, `Z` not defined there, is read as `I`.

`hausdorffDist_girardReach_le` is the corrected bound, with `(1/2 + r‖A‖)`.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], convergence, as printed, fails: at `N = 1` it is [1, Lemma 2]'s bound,
which `girardExample_spec` exceeds. -/
theorem LinearSys.exists_lt_hausdorffDist_girardReach :
    ∃ (sys : LinearSys ℝ 1) (I U : Zonotope (Vec ℝ 1)) (μ r s : ℝ) (N : ℕ),
      0 < ‖toRealMat sys.A‖ ∧ 0 < r ∧ 0 ≤ μ ∧ U.construct = Metric.closedBall 0 μ ∧ 1 ≤ N
      ∧ IsGreatest ((fun x => ‖x‖) '' I.construct) s
      ∧ r * ‖toRealMat sys.A‖ * Real.exp (‖toRealMat sys.A‖ * (N * r))
            * (2 * μ / ‖toRealMat sys.A‖ + (1 / 2 + r) * s)
        < Metric.hausdorffDist
          (⋃ t ∈ Set.Icc (0:ℝ) (N * r), sys.reachSet (S := 𝒵) (Set.Icc 0 t) I U t)
          (⋃ Q ∈ sys.girardReach I μ r (N * r), Q.construct) := by -- --- PROOF ---
  obtain ⟨hnorm, hgr, hd⟩ := LinearSys.girardExample_spec
  have he : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  refine ⟨⟨Matrix.diagonal fun _ => 100⟩, ⟨1, fun _ => 1, fun _ _ => 1⟩, ⟨0, 0, Fin.elim0⟩,
    0, 1 / 100, 2, 1, ?_, by norm_num, le_rfl, ?_, le_rfl, hgr, ?_⟩
  · show 0 < ‖(Matrix.diagonal fun _ => (100:ℝ) : Mat ℝ 1 1)‖
    rw [hnorm]; norm_num
  · rw [Metric.closedBall_zero]
    ext u
    constructor
    · rintro ⟨β, -, rfl⟩; simp
    · rintro rfl; exact ⟨Fin.elim0, fun j => j.elim0, by simp⟩
-- at `N = 1` the algorithm returns `[Q₀]`, and `sup |x| = 2`
  · rw [LinearSys.girardReach_eq]
    simp only [Scalar.toRealMat_real, hnorm, Nat.cast_one, one_mul]
    have hN : ⌈(1 / 100 : ℝ) / (1 / 100)⌉₊ - 1 + 1 = 1 := by norm_num
    have hfold : Finset.univ.fold max 0
        (Zonotope.absBound (⟨1, fun _ => 1, fun _ _ => 1⟩ : Zonotope (Vec ℝ 1))) = 2 := by
      rw [Finset.univ_unique, Finset.fold_singleton]
      simp [Zonotope.absBound]
      norm_num
-- the bound and the radius, at `r‖A‖ = 1`
    rw [hN, List.range_one, List.map_singleton, Function.iterate_zero, id, hfold,
      show (1 / 100 : ℝ) * 100 = 1 by norm_num, show (100 : ℝ) * (1 / 100) = 1 by norm_num,
      show (Real.exp 1 - 1 - 1) * 2 + (Real.exp 1 - 1) / 100 * 0 = 2 * (Real.exp 1 - 2) by ring]
    simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left]
    refine lt_of_lt_of_le ?_ hd
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
