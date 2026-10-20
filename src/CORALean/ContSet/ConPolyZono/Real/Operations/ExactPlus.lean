module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.ExactPlus

@[expose] public section

/-!
# `ConPolyZono.exactPlus`

CORA's `@conPolyZono/exactPlus` [1]: the two sets share their factors, so `PolyZonotope.exactPlus`
of the generator parts adds the points at one and the same factor vector, and the constraints, which
CORA requires to be identical, are kept once. The identifiers are the indices of `Fin p` here
(`hp`: the factor counts agree), so CORA's `mergeExpMatrix` of the identifier vectors is the
identity. CORA's check that the two constraint systems agree is not modelled: the constraints are
the first operand's.

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
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.exactPlus (cPZ₁ cPZ₂ : ConPolyZono α) (hp : cPZ₁.p = cPZ₂.p) : ConPolyZono α :=
  let pZ := cPZ₁.polyZonotope.exactPlus cPZ₂.polyZonotope hp
  { p := pZ.p, h := pZ.h, qI := pZ.q, c := pZ.c, G := pZ.G, E := pZ.E, GI := pZ.GI,
    cons := cPZ₁.cons, cons_eq := cPZ₁.cons_eq, cons_dom := cPZ₁.cons_dom }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
