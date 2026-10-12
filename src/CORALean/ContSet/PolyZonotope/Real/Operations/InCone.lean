import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Defs

/-!
# Cone membership

What the linear program of `aux_inCone` in CORA's `isPolytope` decides: `d = N x`, `x ≥ 0`.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the LP of `aux_inCone` decides: `d = N x` for some `x ≥ 0`. -/
def inCone {m : ℕ} (N : Fin m → α) (d : α) : Prop :=
  ∃ x : Fin m → ℝ, (∀ j, 0 ≤ x j) ∧ d = ∑ j, x j • N j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
