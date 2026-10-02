import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope
import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap

/-!
# `Zonotope.quadMap`, over a floating-point scalar

CORA's `@zonotope/quadMap`: the quadratic map `x ↦ (xᵀ Q_k x)_k` of a zonotope, as a zonotope.
A zonotope is a polynomial zonotope whose exponent matrix is the identity, so the map is
`PolyZonotope.quadMap` there, whose rounded generators `Gᵢᵀ Q Gⱼ` are charged to its error box,
read back as a zonotope. The factors of a zonotope are free in `[-1, 1]`, so the cross products
`αᵢαⱼ` are enclosed rather than tracked, which is why the result is an outer enclosure.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.quadMap (Q : Fin m → Mat 𝕋 n n) (Z : Zonotope 𝕋 n) : Zonotope 𝕋 m :=
  let pZ := Z.polyZonotope
  (PolyZonotope.quadMap Q pZ).zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
