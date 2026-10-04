import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.ExactPlus

/-!
# `ConPolyZono.exactPlus`

CORA's `@conPolyZono/exactPlus` [1]: the two sets share their factors, so `PolyZonotope.exactPlus`
of the generator parts adds the points at one and the same factor vector, and the constraints, which
CORA requires to be identical, are kept once. The identifiers are the indices of `Fin p` here
(`hp`: the factor counts agree), so CORA's `mergeExpMatrix` of the identifier vectors is the
identity. CORA's check that the two constraint systems agree is not modelled: the constraints are
the first operand's.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.exactPlus (cPZ₁ cPZ₂ : ConPolyZono α) (hp : cPZ₁.p = cPZ₂.p) : ConPolyZono α :=
  let pZ := cPZ₁.polyZonotope.exactPlus cPZ₂.polyZonotope hp
  { p := pZ.p, h := pZ.h, q := pZ.q, m := cPZ₁.m, s := cPZ₁.s, c := pZ.c, G := pZ.G, E := pZ.E,
    GI := pZ.GI, A := cPZ₁.A, b := cPZ₁.b, EC := cPZ₁.EC }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
