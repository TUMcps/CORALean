module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.normUb`

CORA's `@ellipsoid/norm_.m` (type `2` only, and only for the centre `c = 0`): `sqrt(max(eig(Q)))`,
the largest singular value of the generator matrix. What is defined here is an upper bound of it:
the Frobenius norm of `G`, plus `‖c‖₂` (zero when `c = 0`, so that the statement needs no side
condition). The Frobenius norm is at least the largest singular value, with equality for rank
one, so this is outer, not CORA's exact value; no eigenvalue is computed. CORA's `-Inf` for an
empty ellipsoid does not arise, an `Ellipsoid` here always holds its centre.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.normUb (E : Ellipsoid n) : ℝ :=
  ‖E.c‖₂ + Real.sqrt (∑ i, ∑ j, E.G i j ^ 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
