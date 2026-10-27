module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularSolutionOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.Global.Err

@[expose] public section

/-!
# The remainder summand of `bPU` is within `n² ‖E‖ |Δt| err U0` of the origin

The interval-matrix summand `E(Δt) Δt U0` of `particularSolutionOuter` ([1, Lemma 2]) lies within
`n² · ‖E(Δt)‖ · |Δt| · err U0` of the origin, entry by entry through Cauchy–Schwarz. Both `bPU`
and its correlated variant add this bound.

## Inputs
* `A` – system matrix
* `U0` – input set
* `Δt` – step length
* `η` – Taylor order

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

/-- The interval-matrix summand of `bPU`, bounded pointwise by `n²` times the remainder's own
operator norm, scaled by the step and `U0`'s size. -/
theorem norm₂_le_of_mem_intervalMulVecSet (A : Mat ℝ n n) {U0 : Set (Vec ℝ n)}
    (hU0 : Bornology.IsBounded U0) (Δt : ℝ) (η : ℕ) : -- --- CONCL ---
    ∀ y ∈ MatExp.intervalMulVecSet (MatExp.expRemainderMat A Δt η) (Δt • U0),
      ‖y‖₂ ≤ (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 := by -- --- PROOF ---
  rintro _ ⟨M, hM, x, hx, rfl⟩
  obtain ⟨x0, hx0, rfl⟩ := hx
  -- each entry of `M.mulVec (Δt • x0)` is a dot product bounded row-by-row, then summed over `n`
  have hrow : ∀ i, |M.mulVec (Δt • x0) i| ≤ (n : ℝ) * ‖MatExp.expRemainderMat A Δt η‖
      * (|Δt| * err U0) := by
    intro i
    have hpt : ‖Δt • x0‖₂ ≤ |Δt| * err U0 := by
      rw [norm₂_smul]
      exact mul_le_mul_of_nonneg_left (norm₂_le_err_of_mem hU0 hx0) (abs_nonneg _)
    -- Cauchy–Schwarz per entry against `|E|`, then the coarse `n` copies of the same bound
    calc |M.mulVec (Δt • x0) i| = |∑ j, M i j * (Δt • x0) j| := rfl
      _ ≤ ∑ j, |M i j * (Δt • x0) j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, ‖MatExp.expRemainderMat A Δt η‖ * ‖Δt • x0‖₂ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          refine mul_le_mul (hM i j |>.trans (abs_entry_le_norm _ i j)) (abs_le_norm₂ _ j)
            (abs_nonneg _) (norm_nonneg _)
      _ = (n : ℝ) * ‖MatExp.expRemainderMat A Δt η‖ * ‖Δt • x0‖₂ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      _ ≤ (n : ℝ) * ‖MatExp.expRemainderMat A Δt η‖ * (|Δt| * err U0) :=
          mul_le_mul_of_nonneg_left hpt (by positivity)
  calc ‖M.mulVec (Δt • x0)‖₂ ≤ ∑ _i : Fin n, (n : ℝ) * ‖MatExp.expRemainderMat A Δt η‖
        * (|Δt| * err U0) :=
        (norm₂_le_sum_abs _).trans (Finset.sum_le_sum fun i _ => hrow i)
    _ = (n : ℝ) ^ 2 * ‖MatExp.expRemainderMat A Δt η‖ * |Δt| * err U0 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
