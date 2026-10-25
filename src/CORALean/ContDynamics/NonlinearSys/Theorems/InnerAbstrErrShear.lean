module

public import CORALean.ContDynamics.NonlinearSys.Operations.InnerAbstrErr
public import CORALean.ContDynamics.NonlinearSys.Theorems.ExpRemainderMatShear

@[expose] public section

/-!
# The abstraction error of the shear vanishes

(13) of [1] at `L = {0}` for the shear's linearization `A = [0 1; 0 0]` and a Taylor order
`η ≥ 1`: every Taylor term maps `0` to `0`, and the remainder interval `E(Δt)` of [2, (20)]
holds `0` (it is `{0}`, `E(Δt, η) = 0`), so `R̂_err(0) = {0}`.

## Inputs
* `Δt` – step size
* `η` – Taylor order

## Hypotheses
* `hη` – Taylor order positive

## Conclusion
* the abstraction error's solution set is the origin

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
* [2] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   21-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise Set


-- =======================================  MAIN THEOREM  ======================================= --

/-- (13): `R̂_err(0) = {0}` for the shear `A = [0 1; 0 0]` and `η ≥ 1`. -/
theorem NonlinearSys.innerAbstrErr_shear (Δt : ℝ) {η : ℕ} (hη : 1 ≤ η) : -- --- CONCL ---
    NonlinearSys.innerAbstrErr η Δt !![0, 1; 0, 0] {0} = {0} := by -- --- PROOF ---
  have h0 : (0 : Mat ℝ 2 2) ∈ Real.MatExp.expRemainderInterval !![0, 1; 0, 0] Δt η :=
    fun j k => by simp [NonlinearSys.expRemainderMat_shear Δt hη]
  have h1 : ∀ M : Mat ℝ 2 2, (fun l => M *ᵥ l) '' ({0} : Set (Vec ℝ 2)) = 0 := fun M => by
    rw [Set.image_singleton, Matrix.mulVec_zero, Set.singleton_zero]
  simp only [NonlinearSys.innerAbstrErr, h1, Finset.sum_const_zero, zero_add]
  rw [← Set.singleton_zero]
  exact Set.biUnion_const ⟨0, h0⟩ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
