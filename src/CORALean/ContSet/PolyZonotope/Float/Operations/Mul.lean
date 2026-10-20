module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MulE
public import CORALean.ContSet.PolyZonotope.Float.Operations.MulGDiff
public import CORALean.ContSet.PolyZonotope.Float.Operations.MulGDown
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mul

@[expose] public section

/-!
# `PolyZonotope.mul`

The exact layer's product, rounded. None of the bookkeeping rounds (`extE`,
`mulE` and `finProdFinEquiv` are all over ℕ), so only the `(h₁+1)(h₂+1)`
generators are computed and charged.

Each is a single product of two stored floats; `mulDown` and `mulUp` bracket it
and the gap goes into the error box, priced by `generatorError` as for `mtimes`.
The guarantee is stated over the nominal sets, so a caller runs `absorbRounding`
first, once, so that a repeated factor's freed coefficients stay identified.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Output
* polynomial zonotope enclosing the product
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.mul (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) (hp : pZ₁.p = pZ₂.p) :
    PolyZonotope (Vec 𝕋 n) where
  p := pZ₁.p
  h := (pZ₁.h + 1) * (pZ₂.h + 1)
  q := 0
  c := fun _ => zero
  G := fun l i => PolyZonotope.mulGDown pZ₁ pZ₂ i l
  E := PolyZonotope.mulE pZ₁ pZ₂ hp
  GI := Fin.elim0
  I_error := PolyZonotope.generatorError (PolyZonotope.mulGDiff pZ₁ pZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
