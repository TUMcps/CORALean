module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpEnclosure

@[expose] public section

/-!
# An entry of `E(Δt,η)` is under the scalar remainder bound

The matrix `E(Δt,η) = e^{|A|Δt} − Σᵢ₌₀^η (|A|Δt)ⁱ/i!` is entrywise under its `l∞` norm, which
`norm_exp_sub_expTaylor_le` bounds by `expRemainderBound (Δt |A|) η`, and `‖Δt |A|‖ = ‖Δt A‖`, as
the row sums of `|A|` are those of `|A|`'s signs. So the scalar bound taken at `Δt A` holds every
entry of the sharper matrix, in absolute value.

## Inputs
* `A` – system matrix
* `r` – step length
* `η` – Taylor order
* `j` – row index
* `k` – column index

## Hypotheses
* `hlt` – the norm of the scaled matrix is small enough for the Taylor order

## Conclusion
* the entry of the remainder matrix is under the scalar remainder bound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every entry of `E(r,η)` is under `expRemainderBound (r A) η` in absolute value. -/
theorem MatExp.expRemainderMat_entry_le_bound (A : Mat ℝ n n) {r : ℝ} (η : ℕ)
    (hlt : ‖r • A‖ / ((η : ℝ) + 2) < 1) (j k : Fin n) : -- --- CONCL ---
    |MatExp.expRemainderMat A r η j k| ≤ MatExp.expRemainderBound (r • A) η := by -- --- PROOF ---
  -- the scaled absolute value has the norm of the scaled matrix
  have hn : ‖r • MatExp.absMat A‖ = ‖r • A‖ := by
    simp [norm_smul, Matrix.linfty_opNorm_def, MatExp.absMat]
  calc |MatExp.expRemainderMat A r η j k|
      ≤ ‖MatExp.expRemainderMat A r η‖ := abs_entry_le_norm _ j k
    _ ≤ MatExp.expRemainderBound (r • MatExp.absMat A) η :=
        norm_exp_sub_expTaylor_le _ η (hn ▸ hlt)
    _ = MatExp.expRemainderBound (r • A) η := by simp only [MatExp.expRemainderBound, hn]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
