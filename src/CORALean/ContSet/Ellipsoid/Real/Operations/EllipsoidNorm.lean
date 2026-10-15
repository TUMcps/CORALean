module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.Global.EuclideanNorm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `Ellipsoid.ellipsoidNorm`

CORA's `@ellipsoid/ellipsoidNorm` at a full-rank ellipsoid, where `isFullDim(E)` holds: `q = Q \ p`
and `sqrt(abs(p' q))`, the norm of `p` with respect to `E` with the center ignored,
`sqrt(|pᵀ Q⁻¹ p|)`. The branch for a degenerate `Q` (an SVD pseudo-inverse with the cut-offs
`1e-10`, and `Inf` for a point outside the range) is not modelled: at a singular `Q` this
definition reads `Matrix`'s junk inverse and means nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ellipsoid/ellipsoidNorm` for a full-rank `E`: `sqrt(|pᵀ Q⁻¹ p|)`. -/
noncomputable def Ellipsoid.ellipsoidNorm (E : Ellipsoid n) (p : Vec ℝ n) : ℝ :=
  let q : Vec ℝ n := E.Q⁻¹ *ᵥ p                -- `Q \ p`
  Real.sqrt |p ⬝ᵥ q|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
