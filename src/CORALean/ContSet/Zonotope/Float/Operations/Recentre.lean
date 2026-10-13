import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.recentre`

The exact layer's `recentre` with the stored centre as the point taken out: the
same generators, the centre zeroed, and the error box widened to hold the
origin, which the stored box need not. `minimum` and `maximum` are exact, so
nothing rounds and the set is the input's moved by exactly its stored centre,
widened by the box's hull with `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The zonotope moved to the origin, keeping its generators, its error box
widened to hold `0`. -/
def Zonotope.recentre (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := Z.h
  c := fun _ => zero
  G := Z.G
  E := ⟨fun i => minimum (Z.E.inf i) zero, fun i => maximum (Z.E.sup i) zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
