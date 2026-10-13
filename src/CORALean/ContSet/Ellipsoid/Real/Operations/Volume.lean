import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# `Ellipsoid.volume`

CORA's `@ellipsoid/volume_`: `V_n sqrt(det Q)`, `V_n = π^(n/2) / Γ(n/2 + 1)` the volume of the
unit `n`-ball, at the shape matrix `Q = G Gᵀ`. CORA's early `vol = 0` for an empty ellipsoid does
not arise (an `Ellipsoid` is never empty), and a singular `Q` gives `det Q = 0` and so `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ellipsoid/volume_`: `π^(n/2) / Γ(n/2 + 1) · sqrt(det Q)` at `Q = G Gᵀ`. -/
noncomputable def Ellipsoid.volume (E : Ellipsoid n) : ENNReal :=
  let Vball : ℝ := Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)  -- unit n-ball
  ENNReal.ofReal (Vball * Real.sqrt E.shape.det)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
