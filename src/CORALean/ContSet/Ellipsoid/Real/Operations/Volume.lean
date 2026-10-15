module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

/-!
# `Ellipsoid.volume`

CORA's `@ellipsoid/volume_`: `V_n sqrt(det Q)`, `V_n = π^(n/2) / Γ(n/2 + 1)` the volume of the
unit `n`-ball, at the shape matrix `Q`. CORA's early `vol = 0` for an empty ellipsoid does
not arise (an `Ellipsoid` is never empty), and a singular `Q` gives `det Q = 0` and so `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ellipsoid/volume_`: `π^(n/2) / Γ(n/2 + 1) · sqrt(det Q)`. -/
noncomputable def Ellipsoid.volume (E : Ellipsoid n) : ENNReal :=
  let Vball : ℝ := Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)  -- unit n-ball
  ENNReal.ofReal (Vball * Real.sqrt E.Q.det)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
