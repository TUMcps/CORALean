module

public import CORALean.ContSet.Capsule.Float.Operations.Reduce

@[expose] public section

/-!
# `Capsule.reduce` encloses

`reduce` is the identity, so it encloses trivially.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.reduce_outer (C : Capsule 𝕋 n) (o : ℕ) :
    C.construct ⊆ (C.reduce o).construct :=
  subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
