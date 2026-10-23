module

public import CORALean.Global.Float.Interfaces
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Comparing the reals two scalars denote, decided

With an exact comparison (`ExactLe`) the propositions `toReal a ≤ toReal b`, `toReal a < toReal b`
and `toReal a = toReal b` are decidable, so an algorithm over the scalar may branch on how the reals
its values denote compare and still run: the order of ℝ itself is not decidable by a program. High
priority, so that over a float scalar the branch is this decision and not ℝ's classical one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ======================================  MAIN INSTANCE  ======================================= --

/-- `toReal a ≤ toReal b`, decided by the exact comparison. -/
instance (priority := high) decidableToRealLe (a b : 𝕋) : Decidable (toReal a ≤ toReal b) :=
  decidable_of_iff _ (ExactLe.le_iff a b)

/-- `toReal a < toReal b`, decided as the negation of the exact comparison the other way. -/
instance (priority := high) decidableToRealLt (a b : 𝕋) : Decidable (toReal a < toReal b) :=
  decidable_of_iff (¬ ExactLe.le b a = true) (by rw [ExactLe.le_iff]; exact not_le)

/-- `toReal a = toReal b`, decided by the exact comparison both ways. -/
instance (priority := high) decidableToRealEq (a b : 𝕋) : Decidable (toReal a = toReal b) :=
  decidable_of_iff (ExactLe.le a b = true ∧ ExactLe.le b a = true)
    (by rw [ExactLe.le_iff, ExactLe.le_iff]; exact le_antisymm_iff.symm)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
