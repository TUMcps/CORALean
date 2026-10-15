module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.isequal`

CORA's `@ellipsoid/isequal.m` for two ellipsoids: both empty, or neither and the shape matrices
`Q` and the centers `q` agree to the tolerance (`withinTol`). Here the tolerance is `0`: the same
`Q` and the same `q`, which is exact, the stored pair determining the set and conversely. An
ellipsoid here always contains its center, so CORA's emptiness case does not arise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ellipsoid/isequal` at tolerance `0`: the same shape matrix and center. -/
def Ellipsoid.isequal (E S : Ellipsoid n) : Prop :=
  E.Q = S.Q ∧ E.q = S.q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
