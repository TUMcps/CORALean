module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.NonlinearSys.Theorems.ExpSmulShear

@[expose] public section

/-!
# The exponential remainder of the shear vanishes

The remainder `E(Δt, η) = e^{|A|Δt} - Σ_{i≤η} (|A|Δt)ⁱ/i!` of [2, (20)], which (13) and (17) of
[1] add to their Taylor sums, is `0` for the shear's `A = [0 1; 0 0]` at every Taylor order
`η ≥ 1`: `|A| = A` and `e^{AΔt} = I + AΔt`, the sum's first two terms. At `η = 0` it is `AΔt`.

## Inputs
* `Δt` – time
* `η` – Taylor order

## Hypotheses
* `hη` – Taylor order positive

## Conclusion
* the remainder matrix is zero

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
* [2] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
  Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 71(1):352-367,
  2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   21-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- [2, (20)]: `E(Δt, η) = e^{|A|Δt} - Σ_{i≤η} (|A|Δt)ⁱ/i! = 0` for the shear `A = [0 1; 0 0]`
and `η ≥ 1`, as `|A| = A`. -/
theorem NonlinearSys.expRemainderMat_shear (Δt : ℝ) {η : ℕ} (hη : 1 ≤ η) : -- --- CONCL ---
    Real.MatExp.expRemainderMat !![0, 1; 0, 0] Δt η = 0 := by -- --- PROOF ---
  have habs : Real.MatExp.absMat (!![0, 1; 0, 0] : Mat ℝ 2 2) = !![0, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Real.MatExp.absMat]
  have htay : Real.MatExp.expTaylor (Δt • (!![0, 1; 0, 0] : Mat ℝ 2 2)) η =
      1 + Δt • !![0, 1; 0, 0] := by
    obtain ⟨k, rfl⟩ : ∃ k, η = k + 1 := ⟨η - 1, by omega⟩
    rw [Real.MatExp.expTaylor, Finset.sum_range_succ', Finset.sum_range_succ',
      Finset.sum_eq_zero fun i _ => by
        rw [smul_pow, NonlinearSys.shear_pow_eq_zero (by omega), smul_zero, smul_zero]]
    simp [add_comm]
  rw [Real.MatExp.expRemainderMat, habs, NonlinearSys.exp_smul_shear, htay, sub_self]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
