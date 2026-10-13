module

public import CORALean.NN.Definitions.ScalarEncloses

@[expose] public section

/-!
# The box itself encloses the identity
`id` is its own enclosure: a point of the box is a point of the box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem identityEnclosure_encloses : ScalarEncloses (id : Interval 𝕋 → Interval 𝕋) id :=
  fun _ _ hl hu => ⟨hl, hu⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
