module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import CORALean.Global.Tensor
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# `Ellipsoid.enclosePointsMaxDist`

The step `maxDist = max(sum(diag(1 ./ nt.^2) * orientedMatrix.^2, 1))` of CORA's
`@ellipsoid/enclosePoints.m` at `method = 'cov'`: the largest, over the points, of the squared
lengths of the points in the coordinates scaled by `nt`. The columns of `O` are the points.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `maxDist = max_j Σᵢ (orientedMatrix(i,j) / ntᵢ)²`. -/
noncomputable def Ellipsoid.enclosePointsMaxDist [NeZero N] (O : Fin N → Vec ℝ n)
    (nt : Vec ℝ n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j => ∑ i, (O j i / nt i) ^ 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
