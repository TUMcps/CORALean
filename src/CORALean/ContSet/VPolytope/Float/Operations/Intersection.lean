module

public import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Float.VPolytope_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `VPolytope.intersection`, over a floating-point scalar

Through boxes, as in the exact layer, and for the same reason: the
intersection's vertices are generally none of either operand's. Each operand's
box already absorbed its error box, intersecting boxes is exact, and the corners
are stored bounds copied — so this operation rounds nowhere, all of its
imprecision being in the detour rather than in the arithmetic.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.intersection (P₁ P₂ : VPolytope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  Interval.vPolytope (P₁.interval.intersection P₂.interval)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
