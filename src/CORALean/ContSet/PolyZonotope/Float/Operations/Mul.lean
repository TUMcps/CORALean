import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.MulE
import CORALean.ContSet.PolyZonotope.Float.Operations.MulGDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.MulGDown
import CORALean.ContSet.PolyZonotope.Real.Operations.Mul

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

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.mul (S₁ S₂ : PolyZonotope 𝕋 n) (hp : S₁.p = S₂.p) : PolyZonotope 𝕋 n where
  p := S₁.p
  h := (S₁.h + 1) * (S₂.h + 1)
  q := 0
  c := fun _ => zero
  G := PolyZonotope.mulGDown S₁ S₂
  E := PolyZonotope.mulE S₁ S₂ hp
  GI := fun _ => Fin.elim0
  err := PolyZonotope.generatorError (PolyZonotope.mulGDiff S₁ S₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
