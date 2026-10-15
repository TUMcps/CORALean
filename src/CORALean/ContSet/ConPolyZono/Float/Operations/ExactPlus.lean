module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ToPolyZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.ExactPlus

@[expose] public section

/-!
# `ConPolyZono.exactPlus` over a floating-point scalar

CORA's `@conPolyZono/exactPlus` [1] on the stored floats: the float `PolyZonotope.exactPlus` of
the two generator parts (the centers added downward, the rounding in the error box, the two
error boxes summed), and the first operand's constraints kept once, as over ℝ.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.exactPlus (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) (hp : cPZ₁.p = cPZ₂.p) :
    ConPolyZono 𝕋 (Vec 𝕋 n) :=
  let pZ := cPZ₁.toPolyZonotope.exactPlus cPZ₂.toPolyZonotope hp
  { p := pZ.p, h := pZ.h, qI := pZ.q, m := cPZ₁.m, q := cPZ₁.q, c := pZ.c, G := pZ.G, E := pZ.E,
    GI := pZ.GI, A := cPZ₁.A, b := cPZ₁.b, R := cPZ₁.R, I_error := pZ.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
