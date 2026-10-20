module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.absBoundError`

`Real.Zonotope.absBound`, rounded, and widened by the error box: how far
coordinate `j` can reach from the origin over the whole `construct`, nominal
part and box together — the center and the generators' absolute sum, `radius`, plus
whichever corner of the box is farther out.

## Inputs
* `Z` – zonotope
* `j` – coordinate

## Output
* reach of coordinate `j` from the origin, error box included
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far coordinate `j` can reach from the origin, over the whole
`construct` — nominal part and error box together. -/
def Zonotope.absBoundError (Z : Zonotope (Vec 𝕋 n)) (j : Fin n) : 𝕋 :=
  addUp (addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j))
    (maximum (absolute (Z.I_error.inf j)) (absolute (Z.I_error.sup j)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
