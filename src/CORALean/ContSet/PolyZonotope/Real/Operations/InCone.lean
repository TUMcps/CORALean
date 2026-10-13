module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Module.Defs

@[expose] public section

/-!
# Cone membership

What the linear program of `aux_inCone` in CORA's `isPolytope` decides: `d = N x`, `x ≥ 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the LP of `aux_inCone` decides: `d = N x` for some `x ≥ 0`. -/
def inCone {m : ℕ} (N : Fin m → α) (d : α) : Prop :=
  ∃ x : Fin m → ℝ, (∀ j, 0 ≤ x j) ∧ d = ∑ j, x j • N j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
