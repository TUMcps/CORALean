module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# The settings of a discrete-time linear backward reach, `∃` reading

The one thing the computed backward set runs on besides the target and the
negated input set: `Ainv`, the inverse the sets are carried back along.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The inverse `Ainv` an `∃` backward reach is run with. -/
structure LinearSysDT.BackReachExistsOptions (𝕋 : Type) [Scalar 𝕋] (n : ℕ) where
  Ainv : Mat 𝕋 n n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
