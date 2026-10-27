module

public import CORALean.ContSet.ContSet.Interfaces
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Set.Pi

@[expose] public section

/-!
# The repaired time-interval inner set drops the shear's unreachable point

`NonlinearSys.minkowskiDiff_chord_subset_reachSetExact`, the chord repair of [1, Prop. 2], at the
data of `convexHull_timeInterval_convex_counterexample`: the shear `ẋ = (x₂, 0)`, `A = [0 1; 0 0]`,
`X₀ = [-1/10, 1/10] × [-1, 1]`, `Δt = 1`, `R_con = 0`, and `C = R̂_err = {0}`, `c = 0`, which is
what (17), (13) give at a Taylor order `η ≥ 1` (derived in
`NonlinearSys.innerMinkDiff_timeInterval_counterexample`). The slice at `t` is `(I + tA)X₀ = R(t)`,
so the repaired set is `R([0, 1])` itself, and `(1/2, 0)`, in (23)'s hull, is not in it.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the midpoint the hull holds is not in the repaired set

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- The repaired [1, Prop. 2] set `⋃_t ((chords(t) ⊖ C) ⊖ R̂_err) + 2c` of the shear from the box,
`C = R̂_err = {0}`, `c = 0`, does not hold `(1/2, 0)`. -/
theorem NonlinearSys.not_mem_minkowskiDiff_chord_shear : -- --- CONCL ---
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let X₀ : Set (Fin 2 → ℝ) := Icc ![-1 / 10, -1] ![1 / 10, 1]
    ![1 / 2, 0] ∉ ⋃ t ∈ Icc (0 : ℝ) 1, (fun s => s + (2 : ℝ) • (0 : Fin 2 → ℝ)) ''
      minkowskiDiff (minkowskiDiff ((fun x₀ => x₀ + (t / 1) • (exp A *ᵥ x₀ + 0 - x₀)) '' X₀)
        {0}) {0} := by -- --- PROOF ---
  intro A X₀
  -- `e^{A} = I + A`, as `A² = 0`
  have hA2 : A ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hexp : exp A = 1 + A := by
    rw [exp_eq_tsum ℝ]
    show ∑' i : ℕ, ((i.factorial : ℝ)⁻¹) • A ^ i = 1 + A
    rw [tsum_eq_sum (s := Finset.range 2) fun b hb => by
      rw [pow_eq_zero_of_le (by simp at hb; omega) hA2, smul_zero]]
    simp [Finset.sum_range_succ]
  have hmd : ∀ T : Set (Fin 2 → ℝ), minkowskiDiff T {0} = T := fun T => by
    ext x; simp [minkowskiDiff]
  simp only [hmd, smul_zero, add_zero, div_one, mem_iUnion, mem_image, not_exists, not_and]
  -- the chord point is `(x₀₁ + t x₀₂, x₀₂)`; at `(1/2, 0)` it starts at `x₀ = (1/2, 0)`
  rintro t - _ ⟨x₀, hx₀, rfl⟩ h
  have e1 := congrFun h 1
  have e0 := congrFun h 0
  simp [hexp, A, Matrix.add_mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  have hb : x₀ 0 ≤ 1 / 10 := by simpa using hx₀.2 0
  rw [e1, mul_zero, add_zero] at e0
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
