import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ParticularRemainderError
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularSolutionOuter
import CORALean.Global.Err

/-!
# Every point of `particularRemainderSet` is within an explicit bound of the origin

`norm₂_le_of_mem_particularRemainderSet`: every point of [1]'s `e^{At_i} E(Δt,η) Δt U` is
within an explicit multiple of `‖E(Δt,η)‖·|Δt|` of the origin.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of `e^{At_i} E(Δt,η) Δt U` is within an explicit multiple of `‖E(Δt,η)‖·|Δt|`
of the origin: `e^{At_i}`'s row norms times what `norm₂_le_of_mem_particularSolutionOuter`
gives the remainder block alone, the Taylor sum being empty from order `η+1`. -/
theorem MatExp.norm₂_le_of_mem_particularRemainderSet (A : Mat ℝ n n) (ti : ℝ)
    {U : Set (Vec ℝ n)} (hU : Bornology.IsBounded U) (Δt : ℝ) (η : ℕ) :
    ∀ y ∈ MatExp.particularRemainderSet A ti U Δt η,
      ‖y‖₂ ≤ (∑ i, ‖(fun j => (exp (ti • A)) i j)‖₂)
        * ((n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U) := by -- --- PROOF ---
  rintro _ ⟨z, hz, rfl⟩
  -- the remainder block is `particularSolutionOuter` with its Taylor sum started past `η`
  have hz' : z ∈ MatExp.particularSolutionOuter A U (η + 1) Δt η := by
    rw [MatExp.particularSolutionOuter, Finset.Ico_self, Finset.sum_empty, zero_add]
    exact hz
  have h := MatExp.norm₂_le_of_mem_particularSolutionOuter A hU (η + 1) Δt η z hz'
  rw [Finset.Ico_self, Finset.sum_empty, zero_add] at h
  exact (norm₂_mulVec_le _ z).trans
    (mul_le_mul_of_nonneg_left h (Finset.sum_nonneg fun i _ => norm₂_nonneg _))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
