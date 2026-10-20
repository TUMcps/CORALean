module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# `SpectraShadow.trace_mul_nonneg`

The trace of a product of two positive semidefinite matrices is nonnegative: with `Z = √Y`,
`tr(M Y) = tr(Z M Zᴴ)`. Half of weak duality for `SpectraShadow`.

## Inputs
* `k` – natural number
* `M` – `k × k` matrix
* `Y` – `k × k` matrix

## Hypotheses
* `hM` – `M.PosSemidef`
* `hY` – `Y.PosSemidef`

## Conclusion
* the trace of `M Y` is nonnegative
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped MatrixOrder


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.trace_mul_nonneg {k : ℕ} {M Y : Mat ℝ k k} (hM : M.PosSemidef)
    (hY : Y.PosSemidef) : 0 ≤ (M * Y).trace := by -- --- PROOF ---
  -- the square root of `Y`, positive semidefinite and Hermitian
  have hY0 : (0 : Mat ℝ k k) ≤ Y := Matrix.nonneg_iff_posSemidef.mpr hY
  have hZ' : (CFC.sqrt Y).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Y)
  have hYZ : CFC.sqrt Y * CFC.sqrt Y = Y := CFC.sqrt_mul_sqrt_self Y hY0
  -- `Z M Zᴴ` is positive semidefinite, so its trace is nonnegative
  have h1 := hM.mul_mul_conjTranspose_same (CFC.sqrt Y)
  rw [hZ'.isHermitian.eq] at h1
  -- and it is the trace of `M Y`, by cyclicity
  have h2 : (M * Y).trace = (CFC.sqrt Y * M * CFC.sqrt Y).trace := by
    calc (M * Y).trace = (M * (CFC.sqrt Y * CFC.sqrt Y)).trace := by rw [hYZ]
      _ = ((M * CFC.sqrt Y) * CFC.sqrt Y).trace := by rw [Matrix.mul_assoc]
      _ = (CFC.sqrt Y * (M * CFC.sqrt Y)).trace := Matrix.trace_mul_comm _ _
      _ = (CFC.sqrt Y * M * CFC.sqrt Y).trace := by rw [Matrix.mul_assoc]
  rw [h2]
  exact h1.trace_nonneg

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
