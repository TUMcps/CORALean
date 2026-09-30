import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# The settings of a discrete-time linear backward reach, `∃` reading

The one thing the computed backward set runs on besides the target and the
negated input set: `Ainv`, the inverse the sets are carried back along.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The inverse `Ainv` an `∃` backward reach is run with. -/
structure LinearSysDT.BackReachExistsOptions (𝕋 : Type) [Scalar 𝕋] (n : ℕ) where
  Ainv : Mat 𝕋 n n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
