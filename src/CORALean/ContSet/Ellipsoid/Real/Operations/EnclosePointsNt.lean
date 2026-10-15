module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import CORALean.Global.Tensor
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# `Ellipsoid.enclosePointsNt`

The step `m1 = max(orientedMatrix, [], 2); m2 = min(orientedMatrix, [], 2); nt = max([m1, m2], [],
2)` of CORA's `@ellipsoid/enclosePoints.m` at `method = 'cov'`: per rotated coordinate the larger
of the maximum and the minimum, which is the maximum `m1` whenever the minimum is not larger (the
maximum of centered values is non-negative). The columns of `O` are the points.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `nt = max([m1, m2], [], 2)`, with `m1` and `m2` the largest and smallest rotated coordinates. -/
noncomputable def Ellipsoid.enclosePointsNt [NeZero N] (O : Fin N → Vec ℝ n) : Vec ℝ n :=
  let m1 := fun i => Finset.univ.sup' Finset.univ_nonempty fun j => O j i
  let m2 := fun i => Finset.univ.inf' Finset.univ_nonempty fun j => O j i
  let nt := fun i => max (m1 i) (m2 i)
  nt

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
