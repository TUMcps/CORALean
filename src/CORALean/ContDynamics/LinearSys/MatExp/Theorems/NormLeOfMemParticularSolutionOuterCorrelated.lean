module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuterCorrelated
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularSolutionOuter
public import CORALean.Global.Err

@[expose] public section

/-!
# Every point of the correlated summand is within an explicit bound of the origin

`norm₂_le_of_mem_particularSolutionOuterCorrelated`: [1]'s `Matrix.sum_mulVec` turns the one
application into the same sum of images `norm₂_sum_le` bounds exactly as
`particularSolutionOuter` does, so `norm₂_le_of_mem_particularCoeffSum_image` reuses its
per-`i` computation directly.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The correlated summand's own matrix, bounded pointwise exactly like the decorrelated sum's:
`Matrix.sum_mulVec` turns the one application into the same sum of images, and `norm₂_sum_le`
plus `aux_norm₂_le_of_mem_particularCoeff_image`'s per-term bound do the rest. -/
theorem aux_norm₂_le_of_mem_particularCoeffSum_image (A : Mat ℝ n n) {U0 : Set (Vec ℝ n)}
    (hU0 : Bornology.IsBounded U0) (i0 η : ℕ) (Δt : ℝ) : -- --- STMT ---
    ∀ y ∈ (fun x => (MatExp.particularCoeffSum A Δt i0 η).mulVec x) '' U0,
      ‖y‖₂ ≤ (∑ i ∈ Finset.Ico i0 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ))) * err U0 := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  have heq : (MatExp.particularCoeffSum A Δt i0 η).mulVec x
      = ∑ i ∈ Finset.Ico i0 (η + 1), (MatExp.particularCoeff A Δt i).mulVec x := by
    simp only [MatExp.particularCoeffSum, Matrix.sum_mulVec]
  rw [heq]
  have hterm : ∀ i ∈ Finset.Ico i0 (η + 1), ‖(MatExp.particularCoeff A Δt i).mulVec x‖₂
      ≤ (∑ j, ‖(fun k => (A ^ i) j k)‖₂) * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ))
        * err U0 := fun i _ => aux_norm₂_le_of_mem_particularCoeff_image A hU0 Δt i _
      (Set.mem_image_of_mem (fun x => (MatExp.particularCoeff A Δt i).mulVec x) hx)
  calc ‖∑ i ∈ Finset.Ico i0 (η + 1), (MatExp.particularCoeff A Δt i).mulVec x‖₂
      ≤ ∑ i ∈ Finset.Ico i0 (η + 1), ‖(MatExp.particularCoeff A Δt i).mulVec x‖₂ :=
        norm₂_sum_le _ _
    _ ≤ ∑ i ∈ Finset.Ico i0 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
          * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0 := Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.Ico i0 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
          * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ))) * err U0 := by rw [Finset.sum_mul]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of the correlated summand is within this explicit `Δt`-polynomial of the origin —
the same one `norm₂_le_of_mem_particularSolutionOuter` gives the decorrelated summand. -/
theorem MatExp.norm₂_le_of_mem_particularSolutionOuterCorrelated (A : Mat ℝ n n)
    {U0 : Set (Vec ℝ n)} (hU0 : Bornology.IsBounded U0) (i0 : ℕ) (Δt : ℝ) (η : ℕ) : -- --- STMT ---
    ∀ y ∈ MatExp.particularSolutionOuterCorrelated A U0 i0 Δt η,
      ‖y‖₂ ≤ (∑ i ∈ Finset.Ico i0 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
          * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0)
        + (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 := by -- --- PROOF ---
  rintro y hy
  rw [MatExp.particularSolutionOuterCorrelated, Set.mem_add] at hy
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := hy
  have h1 : ‖y1‖₂ ≤ (∑ i ∈ Finset.Ico i0 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
      * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ))) * err U0 :=
    aux_norm₂_le_of_mem_particularCoeffSum_image A hU0 i0 η Δt y1 hy1
  have h2 : ‖y2‖₂ ≤ (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 :=
    aux_norm₂_le_of_mem_intervalMulVecSet A hU0 Δt η y2 hy2
  calc ‖y1 + y2‖₂ ≤ ‖y1‖₂ + ‖y2‖₂ := norm₂_add_le _ _
    _ ≤ (∑ i ∈ Finset.Ico i0 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
          * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ))) * err U0
        + (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 := add_le_add h1 h2
    _ = (∑ i ∈ Finset.Ico i0 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
          * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0)
        + (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 := by rw [Finset.sum_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
