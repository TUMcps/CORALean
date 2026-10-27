module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.Global.Err

@[expose] public section

/-!
# One Taylor summand of `bPU` is within a polynomial in `Δt` of the origin

The `i`-th summand `Ãᵢ U0` of `particularSolutionOuter` ([1, Lemma 2]) lies within
`Σⱼ ‖(Aⁱ)ⱼ‖₂ · |Δt|ⁱ⁺¹/(i+1)! · err U0` of the origin. Both `bPU` and its correlated variant sum
these bounds.

## Inputs
* `A` – system matrix
* `U0` – input set
* `Δt` – step length
* `i` – Taylor index

## Hypotheses
* `hU0` – input set bounded

## Conclusion
* every point of the summand is within the bound

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- One `Ãᵢ`-scaled summand of `bPU`, bounded pointwise by its own polynomial order in `Δt`. -/
theorem norm₂_le_of_mem_particularCoeff_image (A : Mat ℝ n n) {U0 : Set (Vec ℝ n)}
    (hU0 : Bornology.IsBounded U0) (Δt : ℝ) (i : ℕ) : -- --- CONCL ---
    ∀ y ∈ (fun x => (MatExp.particularCoeff A Δt i).mulVec x) '' U0,
      ‖y‖₂ ≤ (∑ j, ‖(fun k => (A ^ i) j k)‖₂) * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ))
        * err U0 := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  have hcoeff : (MatExp.particularCoeff A Δt i).mulVec x
      = (Δt ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • (A ^ i).mulVec x := by
    simp only [MatExp.particularCoeff, Matrix.smul_mulVec]
  have h1 : ‖(A ^ i).mulVec x‖₂ ≤ (∑ j, ‖(fun k => (A ^ i) j k)‖₂) * err U0 :=
    (norm₂_mulVec_le _ x).trans (mul_le_mul_of_nonneg_left (norm₂_le_err_of_mem hU0 hx)
      (Finset.sum_nonneg fun j _ => norm₂_nonneg _))
  -- pull the scalar factor `Δtⁱ⁺¹/(i+1)!` out, then bound the matrix's own image by `h1`
  rw [hcoeff, norm₂_smul]
  have habs : |Δt ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)|
      = |Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ) := by
    rw [abs_div, abs_pow, Nat.abs_cast]
  have hmul := mul_le_mul_of_nonneg_left h1
    (abs_nonneg (Δt ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)))
  rw [habs] at hmul
  calc |Δt ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)| * ‖(A ^ i).mulVec x‖₂
      = |Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ) * ‖(A ^ i).mulVec x‖₂ := by rw [habs]
    _ ≤ |Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)
        * ((∑ j, ‖(fun k => (A ^ i) j k)‖₂) * err U0) := hmul
    _ = (∑ j, ‖(fun k => (A ^ i) j k)‖₂)
        * (|Δt| ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) * err U0 := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
