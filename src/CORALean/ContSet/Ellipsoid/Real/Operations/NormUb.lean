module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.normUb`

CORA's `@ellipsoid/norm_.m` (type `2` only, and only for the center `q = 0`): `sqrt(max(eig(Q)))`.
What is defined here is an upper bound of it: `sqrt(trace(Q))`, plus `‖q‖₂` (zero when `q = 0`, so
that the statement needs no side condition). The trace is the sum of the eigenvalues, all
nonnegative, so it is at least the largest, with equality for rank one: this is outer, not CORA's
exact value, and no eigenvalue is computed. CORA's `-Inf` for an empty ellipsoid does not arise,
an `Ellipsoid` here always holds its center.

## Inputs
* `E` – ellipsoid

## Output
* `√trace(Q) + ‖q‖`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.normUb (E : Ellipsoid n) : ℝ :=
  ‖E.q‖₂ + Real.sqrt E.Q.trace

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
