import CORALean.ContSet.ConPolyZono.Float.Operations.ToPolyZonotope
import CORALean.ContSet.PolyZonotope.Float.Operations.ExactPlus

/-!
# `ConPolyZono.exactPlus` over a floating-point scalar

CORA's `@conPolyZono/exactPlus` [1] on the stored floats: the float `PolyZonotope.exactPlus` of
the two generator parts (the centres added downward, the rounding in the error box, the two
error boxes summed), and the first operand's constraints kept once, as over ℝ.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.exactPlus (cPZ₁ cPZ₂ : ConPolyZono 𝕋 n) (hp : cPZ₁.p = cPZ₂.p) :
    ConPolyZono 𝕋 n :=
  let pZ := cPZ₁.toPolyZonotope.exactPlus cPZ₂.toPolyZonotope hp
  { p := pZ.p, h := pZ.h, q := pZ.q, m := cPZ₁.m, s := cPZ₁.s, c := pZ.c,
    G := fun i l => pZ.G l i, E := pZ.E, GI := fun i j => pZ.GI j i, A := cPZ₁.A, b := cPZ₁.b,
    EC := cPZ₁.EC, err := pZ.err }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
