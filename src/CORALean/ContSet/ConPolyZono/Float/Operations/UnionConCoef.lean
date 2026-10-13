import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConInt
import CORALean.Global.Float.IntRound

/-!
# `ConPolyZono.unionConCoef`

The stored coefficients of the selector row: each integer of `unionConInt` rounded
down. Exact wherever the scalar holds the integer, and an enclosure otherwise,
which `unionConErr` charges to the row's bound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The selector row's integer coefficients, stored from below. -/
def ConPolyZono.unionConCoef (p₁ p₂ : ℕ) :
    Fin (2 + (p₁ + p₁ + (p₂ + p₂ + (p₁ * p₂ + p₁ * p₂)))) → 𝕋 :=
  fun l => intDown (ConPolyZono.unionConInt p₁ p₂ l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
