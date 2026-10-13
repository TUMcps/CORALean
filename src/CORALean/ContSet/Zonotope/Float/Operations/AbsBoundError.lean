import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.absBoundError`

`Real.Zonotope.absBound`, rounded, and widened by the error box: how far
coordinate `j` can reach from the origin over the whole `construct`, nominal
part and box together — the centre and the generators' absolute sum, `radius`, plus
whichever corner of the box is farther out.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far coordinate `j` can reach from the origin, over the whole
`construct` — nominal part and error box together. -/
def Zonotope.absBoundError (Z : Zonotope (Vec 𝕋 n)) (j : Fin n) : 𝕋 :=
  addUp (addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j))
    (maximum (absolute (Z.E.inf j)) (absolute (Z.E.sup j)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
