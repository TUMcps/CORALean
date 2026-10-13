module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ParticularSolutionTauErrorBound
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionTauError
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularSolutionOuter
public import CORALean.Global.Err

@[expose] public section

/-!
# `particularSolutionTauError` is within `√n` times its own explicit bound

[1, Lemma 4]'s bound: `norm₂_mulVec_le` carries `norm₂_le_of_mem_particularSolutionOuter`'s
bound through the fixed matrix `e^{Atk}`, and `Finset.Ico 0 (η+1) = Finset.range (η+1)`
matches `bPU` to it.

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

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every point `e^{Atk}` sends `bPU(Δt)` to is within `particularSolutionTauErrorBound`'s reach
of the origin: `norm₂_mulVec_le` carries `norm₂_le_of_mem_particularSolutionOuter`'s bound through
the fixed matrix `e^{Atk}`, and `Finset.Ico 0 (η+1) = Finset.range (η+1)` matches `bPU` to it. -/
theorem aux_norm₂_le_of_mem_particularSolutionTauError_set (A : Mat ℝ n n) (tk : ℝ)
    {U0 : Set (Vec ℝ n)} (hU0 : Bornology.IsBounded U0) (Δt : ℝ) (η : ℕ) :
    ∀ z ∈ (fun x => (exp (tk • A)).mulVec x) '' MatExp.particularSolutionOuter A U0 0 Δt η,
      ‖z‖₂ ≤ MatExp.particularSolutionTauErrorBound A tk U0 Δt η := by -- --- PROOF ---
  rintro _ ⟨y, hy, rfl⟩
  have hrange : Finset.Ico 0 (η + 1) = Finset.range (η + 1) := Nat.Ico_zero_eq_range (η + 1)
  have hy' := MatExp.norm₂_le_of_mem_particularSolutionOuter A hU0 0 Δt η y hy
  rw [hrange] at hy'
  exact (norm₂_mulVec_le _ y).trans (mul_le_mul_of_nonneg_left hy'
    (Finset.sum_nonneg fun i _ => norm₂_nonneg _))


-- =======================================  MAIN THEOREM  ======================================= --

/-- `particularSolutionTauError` is within `√n` times its own explicit bound. -/
theorem MatExp.particularSolutionTauError_le (A : Mat ℝ n n) (tk : ℝ) {U0 : Set (Vec ℝ n)}
    (hU0 : Bornology.IsBounded U0) (Δt : ℝ) (η : ℕ) :
    MatExp.particularSolutionTauError A tk U0 Δt η
      ≤ Real.sqrt n * MatExp.particularSolutionTauErrorBound A tk U0 Δt η := by -- --- PROOF ---
  have hr : (0:ℝ) ≤ MatExp.particularSolutionTauErrorBound A tk U0 Δt η := by
    have hterm : ∀ i ∈ Finset.range (η + 1), (0:ℝ) ≤ (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0 := fun i _ =>
      mul_nonneg (mul_nonneg (Finset.sum_nonneg fun j _ => norm₂_nonneg _)
        (div_nonneg (pow_nonneg (abs_nonneg _) _) (Nat.cast_nonneg _))) (err_nonneg U0)
    have h1 : (0:ℝ) ≤ ∑ i ∈ Finset.range (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0 :=
      Finset.sum_nonneg hterm
    have h2 : (0:ℝ) ≤ (n:ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (abs_nonneg _))
        (err_nonneg U0)
    have h3 : (0:ℝ) ≤ ∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂ :=
      Finset.sum_nonneg fun i _ => norm₂_nonneg _
    exact mul_nonneg h3 (by linarith)
  exact err_le_of_forall_norm₂_le hr
    (aux_norm₂_le_of_mem_particularSolutionTauError_set A tk hU0 Δt η)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
