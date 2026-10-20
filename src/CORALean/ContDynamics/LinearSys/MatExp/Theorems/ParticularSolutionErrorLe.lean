module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ParticularSolutionErrorBound
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionError
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularSolutionOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfMemParticularSolutionOuterCorrelated
public import CORALean.Global.Err

@[expose] public section

/-!
# `particularSolutionError` is within its own explicit bound

[1, Lemma 2]'s bound: both `err`-summands' underlying sets are within
`particularSolutionErrorBound`'s own reach, half of it each.

## Inputs
* `A` – system matrix
* `tk` – step start time
* `U0` – input set
* `Δt` – step length
* `η` – Taylor order

## Hypotheses
* `hU0` – input set bounded

## Conclusion
* the error is under the root of the dimension times its explicit bound

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

/-- Both `err`-summands' underlying sets are within `particularSolutionErrorBound`'s own reach,
half of it each — the same computation `aux_norm₂_le_of_mem_particularSolutionTauError_set` does
for `bPU`, once for the correlated summand and once for the decorrelated one. -/
theorem aux_norm₂_le_of_mem_particularSolutionError_set (A : Mat ℝ n n) (tk : ℝ)
    {U0 : Set (Vec ℝ n)} (hU0 : Bornology.IsBounded U0) (Δt : ℝ) (η : ℕ) : -- --- CONCL ---
    (∀ z ∈ (fun x => (exp (tk • A)).mulVec x)
          '' MatExp.particularSolutionOuterCorrelated A U0 1 Δt η,
        ‖z‖₂ ≤ MatExp.particularSolutionErrorBound A tk U0 Δt η / 2) ∧
      (∀ z ∈ (fun x => (exp (tk • A)).mulVec x) '' MatExp.particularSolutionOuter A U0 1 Δt η,
        ‖z‖₂ ≤ MatExp.particularSolutionErrorBound A tk U0 Δt η / 2) := by -- --- PROOF ---
  have hCnn : (0:ℝ) ≤ ∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂ :=
    Finset.sum_nonneg fun i _ => norm₂_nonneg _
  have heq : MatExp.particularSolutionErrorBound A tk U0 Δt η / 2
      = (∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂) *
        ((∑ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
            * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0)
          + (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0) := by
    rw [MatExp.particularSolutionErrorBound]; ring
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    have hy' := MatExp.norm₂_le_of_mem_particularSolutionOuterCorrelated A hU0 1 Δt η y hy
    rw [heq]
    exact (norm₂_mulVec_le _ y).trans (mul_le_mul_of_nonneg_left hy' hCnn)
  · rintro _ ⟨y, hy, rfl⟩
    have hy' := MatExp.norm₂_le_of_mem_particularSolutionOuter A hU0 1 Δt η y hy
    rw [heq]
    exact (norm₂_mulVec_le _ y).trans (mul_le_mul_of_nonneg_left hy' hCnn)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `particularSolutionError` is within its own explicit bound. -/
theorem MatExp.particularSolutionError_le (A : Mat ℝ n n) (tk : ℝ) {U0 : Set (Vec ℝ n)}
    (hU0 : Bornology.IsBounded U0) (Δt : ℝ) (η : ℕ) : -- --- CONCL ---
    MatExp.particularSolutionError A tk U0 Δt η
      ≤ Real.sqrt n * MatExp.particularSolutionErrorBound A tk U0 Δt η := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := aux_norm₂_le_of_mem_particularSolutionError_set A tk hU0 Δt η
  -- the bound itself is nonnegative, being a sum of products of norms and `err`
  have hr : (0:ℝ) ≤ MatExp.particularSolutionErrorBound A tk U0 Δt η / 2 := by
    have hterm : ∀ i ∈ Finset.Ico 1 (η + 1), (0:ℝ) ≤ (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0 := fun i _ =>
      mul_nonneg (mul_nonneg (Finset.sum_nonneg fun j _ => norm₂_nonneg _)
        (div_nonneg (pow_nonneg (abs_nonneg _) _) (Nat.cast_nonneg _))) (err_nonneg U0)
    have h1' : (0:ℝ) ≤ ∑ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0 := Finset.sum_nonneg hterm
    have h2' : (0:ℝ) ≤ (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (abs_nonneg _))
        (err_nonneg U0)
    have h3' : (0:ℝ) ≤ ∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂ :=
      Finset.sum_nonneg fun i _ => norm₂_nonneg _
    rw [MatExp.particularSolutionErrorBound]
    have : (0:ℝ) ≤ 2 * (∑ i, ‖(fun j => (exp (tk • A)) i j)‖₂)
        * ((∑ i ∈ Finset.Ico 1 (η + 1), (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
            * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0)
          + (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  -- `err`'s bridge to a pointwise bound, once for each summand, then folded back together
  have h1'' := err_le_of_forall_norm₂_le hr h1
  have h2'' := err_le_of_forall_norm₂_le hr h2
  rw [MatExp.particularSolutionError]
  have hsplit : Real.sqrt n * MatExp.particularSolutionErrorBound A tk U0 Δt η
      = Real.sqrt n * (MatExp.particularSolutionErrorBound A tk U0 Δt η / 2)
        + Real.sqrt n * (MatExp.particularSolutionErrorBound A tk U0 Δt η / 2) := by ring
  rw [hsplit]
  exact add_le_add h1'' h2''

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
