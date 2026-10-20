module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ToPolyZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.ExactPlus

@[expose] public section

/-!
# `ConPolyZono.exactPlus` over a floating-point scalar

CORA's `@conPolyZono/exactPlus` [1] on the stored floats: the float `PolyZonotope.exactPlus` of
the two generator parts (the centers added downward, the rounding in the error box, the two
error boxes summed), and the first operand's constraints kept once, as over ℝ.

## Inputs
* `cPZ₁` – first summand
* `cPZ₂` – second summand

## Hypotheses
* `hp` – both have the same number of factors

## Output
* Minkowski sum with shared factors

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.exactPlus (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) (hp : cPZ₁.p = cPZ₂.p) :
    ConPolyZono 𝕋 (Vec 𝕋 n) :=
  let pZ := cPZ₁.toPolyZonotope.exactPlus cPZ₂.toPolyZonotope hp
  { p := pZ.p, h := pZ.h, qI := pZ.q, c := pZ.c, G := pZ.G, E := pZ.E, GI := pZ.GI,
    cons := cPZ₁.cons, cons_eq := cPZ₁.cons_eq, cons_dom := cPZ₁.cons_dom, I_error := pZ.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
