module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.representsa_point` over a floating-point scalar

`conPolyZono/representsa_` at `point`, as CORA tests it: no generator column of either block.
The test reads two sizes and no stored number, so it is the same `Bool` as the exact layer's on
the nominal set; what it guarantees at float is `construct_subset_of_representsa_point`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conPolyZono/representsa_` at `point`: no generator column of either block. -/
def ConPolyZono.representsa_point (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Bool :=
  cPZ.h == 0 && cPZ.qI == 0

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
