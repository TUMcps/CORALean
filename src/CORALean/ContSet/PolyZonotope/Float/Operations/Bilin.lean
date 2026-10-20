module

public import CORALean.ContSet.PolyZonotope.Float.Operations.BilinE
public import CORALean.ContSet.PolyZonotope.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGDown
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

@[expose] public section

/-!
# `PolyZonotope.bilin`, over a floating-point scalar

The float counterpart of `Real.PolyZonotope.bilin` at a family of bilinear forms `x ↦ y ↦ xᵀ Qₖ y`
(`Real.PolyZonotope.quadBilin`). Two polynomial zonotopes over the *same* factors, `hp` lining
their counts up; the result has the `(h₁+1)(h₂+1)` generators `Gᵢᵀ Q Gⱼ` rounded down, the exponent
column the added one, and the rounding paid into the error box.

Sound only where both operands have an empty independent block and an empty error box, a bilinear
map being no more additive than a quadratic one, so `absorbRounding` comes first at every caller:
`quadMapDep` is this at one set paired with itself, `quadMapMixed` at a product of two.

## Inputs
* `Q` – family of bilinear form matrices
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Output
* polynomial zonotope enclosing the bilinear image
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.bilin (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n))
    (hp : pZ₁.p = pZ₂.p) : PolyZonotope (Vec 𝕋 m) where
  p := pZ₁.p
  h := (pZ₁.h + 1) * (pZ₂.h + 1)
  q := 0
  c := fun _ => FloatOps.zero
  G := fun l i => PolyZonotope.bilinGDown Q pZ₁ pZ₂ i l
  E := PolyZonotope.bilinE pZ₁ pZ₂ hp
  GI := Fin.elim0
  I_error := PolyZonotope.generatorError (PolyZonotope.bilinGDiff Q pZ₁ pZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
