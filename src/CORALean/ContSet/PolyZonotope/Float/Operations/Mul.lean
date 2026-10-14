module

public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MulE
public import CORALean.ContSet.PolyZonotope.Float.Operations.MulGDiff
public import CORALean.ContSet.PolyZonotope.Float.Operations.MulGDown
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mul

@[expose] public section

/-!
# `PolyZonotope.mul`

The exact layer's product, rounded. None of the bookkeeping rounds — `extE`,
`mulE` and `finProdFinEquiv` are all over ℕ — so only the `(h₁+1)(h₂+1)`
generators are computed, and only they are charged.

Each is a single product of two stored floats, where `quadMap`'s is a bilinear
form and has to carry the middle vector as an interval. `mulDown` and `mulUp`
bracket it directly, and the gap between them goes into the error box, which
`generatorError` prices exactly as it does for `mtimes`.

The guarantee is stated over the nominal sets, so this is an operation for a
caller that has run `dependent` — the one thing here that empties both the
independent block and the box — and run it once, so that a repeated factor's
freed coefficients stay identified.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


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
