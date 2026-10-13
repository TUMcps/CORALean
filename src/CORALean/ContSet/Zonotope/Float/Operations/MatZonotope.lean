import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# A zonotope as a one-column matrix zonotope

CORA's `zonotope/matZonotope`: the centre and each generator reshaped to an `n × 1` matrix,
which the matrix zonotope's product with a matrix zonotope of conforming shape then consumes.
Nothing is rounded: the entries, and the error box with them, are moved as stored.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.matZonotope (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Mat 𝕋 n 1) where
  h := Z.h
  c := fun i _ => Z.c i
  G := fun k i _ => Z.G k i
  E := ⟨fun i _ => Z.E.inf i, fun i _ => Z.E.sup i⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
