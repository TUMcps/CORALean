import CORALean.ContDynamics.LinearSys.Operations.EntryIsFloat

/-!
# A `true` from the entry test is a proof

When `LinearSys.entryIsFloat a x` answers `true`, the real value of `x` is that of `a`: `le` is
sound when it answers `true`, and both directions hold.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.entryIsFloat_sound {a x : 𝕋} (h : LinearSys.entryIsFloat a x = true) :
    toReal x = toReal a := by
  unfold LinearSys.entryIsFloat at h
  rw [Bool.and_eq_true] at h
  exact le_antisymm (toReal_le_of_le h.2) (toReal_le_of_le h.1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
