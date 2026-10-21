module

public import CORALean.ContDynamics.NonlinearSys.Operations.InnerCurvatureError
public import CORALean.ContDynamics.NonlinearSys.Theorems.ExpRemainderMatShear

@[expose] public section

/-!
# The curvature error of the shear vanishes

(17) of [1] for the shear's linearization `A = [0 1; 0 0]`, a Taylor order `η ≥ 1`, `w = 0` and
a nonempty box: `F` of [2, (19)] sums `Aⁱ`, `i ≥ 2`, all `0`, and the remainder `E(Δt, η) = 0`,
so `F = {0}`; `G` of [2, (28)] is not `0` (its `i = 2` term is a multiple of `A`) but holds
`0` and multiplies `w = 0`. Hence `C = F box(X₀) ⊕ G w = {0}`.

## Inputs
* `Δt` – step size
* `η` – Taylor order
* `B` – shifted box

## Hypotheses
* `hη` – Taylor order positive
* `hB` – box nonempty

## Conclusion
* the curvature error is the origin

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

open Matrix Pointwise Set


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [2, (19)]: `F = ⊕_{i=2}^η […] Aⁱ/i! ⊕ E = {0}` for the shear and `η ≥ 1`. -/
theorem NonlinearSys.aux_shear_depCurvatureF (Δt : ℝ) {η : ℕ} (hη : 1 ≤ η) : -- --- CONCL ---
    (STL.depCurvatureF !![0, 1; 0, 0] Δt η).construct = {0} := by -- --- PROOF ---
  have hT : ∀ i j k, Real.MatExp.corrTerm !![0, 1; 0, 0] Δt (i + 2) j k = 0 := fun i j k => by
    simp [Real.MatExp.corrTerm, NonlinearSys.shear_pow_eq_zero (i := i + 2) (by omega)]
  ext M
  simp only [Real.Interval.construct, STL.depCurvatureF, hT,
    NonlinearSys.expRemainderMat_shear Δt hη, min_self, max_self, Finset.sum_const_zero,
    Matrix.zero_apply, sub_zero, add_zero, mem_setOf_eq, mem_singleton_iff, Entrywise.entry_mat]
  constructor
  · intro h; ext j k; exact le_antisymm (h (j, k)).2 (h (j, k)).1
  · rintro rfl p; simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- (17): `C = F box(X₀) ⊕ G w = {0}` for the shear `A = [0 1; 0 0]`, `η ≥ 1`, `w = 0` and a
nonempty box, though `G ≠ 0`. -/
theorem NonlinearSys.innerCurvatureError_shear (Δt : ℝ) {η : ℕ} (hη : 1 ≤ η)
    {B : Set (Vec ℝ 2)} (hB : B.Nonempty) : -- --- CONCL ---
    NonlinearSys.innerCurvatureError η Δt !![0, 1; 0, 0] B 0 = {0} := by -- --- PROOF ---
  have hG : (0 : Mat ℝ 2 2) ∈ (STL.depCurvatureG !![0, 1; 0, 0] Δt η).construct := fun p => by
    simp only [STL.depCurvatureG, NonlinearSys.expRemainderMat_shear Δt hη,
      Entrywise.entry_mat, Matrix.zero_apply, mul_zero, sub_zero, add_zero]
    exact ⟨Finset.sum_nonpos fun _ _ => min_le_right _ _,
      Finset.sum_nonneg fun _ _ => le_max_right _ _⟩
  have h1 : (⋃ M ∈ (STL.depCurvatureF !![0, 1; 0, 0] Δt η).construct,
      (fun x => M *ᵥ x) '' B) = {0} := by
    rw [NonlinearSys.aux_shear_depCurvatureF Δt hη]; simp [hB.image_const]
  have h2 : (⋃ N ∈ (STL.depCurvatureG !![0, 1; 0, 0] Δt η).construct,
      ({N *ᵥ (0 : Vec ℝ 2)} : Set _)) = {0} := by
    simp only [Matrix.mulVec_zero]
    exact Set.biUnion_const ⟨0, hG⟩ _
  simp only [NonlinearSys.innerCurvatureError, h1, h2, Set.singleton_add_singleton, add_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
