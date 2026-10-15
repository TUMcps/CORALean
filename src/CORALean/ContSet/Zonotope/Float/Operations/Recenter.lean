module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.recenter`

The exact layer's `recenter` with the stored center as the point taken out: the
same generators, the center zeroed, and the error box widened to hold the
origin, which the stored box need not. `minimum` and `maximum` are exact, so
nothing rounds and the set is the input's moved by exactly its stored center,
widened by the box's hull with `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The zonotope moved to the origin, keeping its generators, its error box
widened to hold `0`. -/
def Zonotope.recenter (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := Z.h
  c := fun _ => zero
  G := Z.G
  I_error := ⟨fun i => minimum (Z.I_error.inf i) zero, fun i => maximum (Z.I_error.sup i) zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
