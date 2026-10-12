import CORALean.ContSet.PolyZonotope.Float.Operations.CubMapGDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.ExtE
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

/-!
# `PolyZonotope.cubMapDep`

CORA's `@polyZonotope/cubMap` (`aux_cubMapSingle`) at a set with no independent block and no error
box, on the stored floats: the cubic map `{ (xᵀ T x) * x | x ∈ pZ }` of a polynomial zonotope is a
polynomial zonotope again, the factors being shared, so `m_a m_b m_c` is one monomial, in the
exponent column `E_a + E_b + E_c` (the centre has the zero column). The centre of the result is
`0`: the constant monomial is the generator `(0, 0, 0)`. The generators are stored rounded down and
the gap to rounding up is charged to the error box. Every ordered triple is kept, CORA's
symmetrized pairs and `removeRedundantExponents` leaving the polynomial unchanged. Sound only where
the operand's independent block and error box are empty, so nothing outside `cubMap` calls it.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.cubMapDep (T : Fin m → Fin n → Mat 𝕋 n n) (pZ : PolyZonotope 𝕋 n) :
    PolyZonotope 𝕋 m where
  p := pZ.p
  h := (pZ.h + 1) * (pZ.h + 1) * (pZ.h + 1)
  q := 0
  c := fun _ => zero
  G := fun l i => PolyZonotope.cubMapGDown T pZ i l
  E := fun k l =>
    let t := Real.Zonotope.cubIdx (pZ.h + 1) (pZ.h + 1) (pZ.h + 1) l
    PolyZonotope.extE pZ k t.1.1 + PolyZonotope.extE pZ k t.1.2 + PolyZonotope.extE pZ k t.2
  GI := Fin.elim0
  err := PolyZonotope.generatorError (PolyZonotope.cubMapGDiff T pZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
