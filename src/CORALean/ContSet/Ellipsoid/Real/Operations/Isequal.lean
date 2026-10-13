module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.isequal`

CORA's `@ellipsoid/isequal.m` for two ellipsoids: both empty, or neither and the shape matrices
`Q` and the centres `q` agree to the tolerance (`withinTol`). Here the ellipsoid is stored by its
generators `G` with `Q = G Gᵀ`, and the tolerance is `0`: the test compares the representation,
the same number of generators, the same centre and the same `G`. That is stricter than CORA's on
`Q` (two generator matrices with `G Gᵀ = H Hᵀ` denote the same ellipsoid), so the test is sound,
not exact. An ellipsoid here always contains its centre, so CORA's emptiness case does not arise.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ellipsoid/isequal` at tolerance `0`, on the generator form: same count, centre and `G`. -/
def Ellipsoid.isequal (E S : Ellipsoid n) : Prop :=
  ∃ e : E.k = S.k, E.q = S.q ∧ ∀ i j, E.G i j = S.G i (Fin.cast e j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
