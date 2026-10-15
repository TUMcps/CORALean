module

public import CORALean.ContSet.Ellipsoid.Real.Operations.OfShape

@[expose] public section

/-!
# CORA's ellipsoid fields before its constructor's check

CORA's `ellipsoid(Q, q)` checks that `Q` is symmetric and positive semi-definite and refuses
otherwise. `Unchecked` holds the two fields as given, with no such proof, and reads them as
`Ellipsoid.ofShape` does: the ellipsoid of `Q` where `Q` is positive semi-definite, the center
alone where the constructor would refuse. It is what a float ellipsoid's stored fields read as
reals are (`Float.Ellipsoid`'s nominal part): reading them needs no decision, so the float layer
runs, and the decision is made here, in the set they denote.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- CORA's fields `Q` and `q`, not yet checked. -/
structure Ellipsoid.Unchecked (n : ℕ) where
  /-- The shape matrix, CORA's `Q`, not known to be positive semi-definite. -/
  Q : Mat ℝ n n
  /-- The center, CORA's `q`. -/
  q : Vec ℝ n

/-- The ellipsoid CORA's constructor makes of the fields. -/
noncomputable abbrev Ellipsoid.Unchecked.ellipsoid (D : Ellipsoid.Unchecked n) : Ellipsoid n :=
  Ellipsoid.ofShape D.Q D.q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
