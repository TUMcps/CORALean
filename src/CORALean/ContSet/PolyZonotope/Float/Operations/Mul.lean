import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
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
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Generator `(i, j)` of the product, rounded down: one multiplication per
coordinate. -/
def PolyZonotope.mulGDown (S₁ S₂ : PolyZonotope 𝕋 n) :
    Mat 𝕋 n ((S₁.h + 1) * (S₂.h + 1)) :=
  fun i l => mulDown (PolyZonotope.extG S₁ i (finProdFinEquiv.symm l).1)
    (PolyZonotope.extG S₂ i (finProdFinEquiv.symm l).2)

def PolyZonotope.mulGUp (S₁ S₂ : PolyZonotope 𝕋 n) :
    Mat 𝕋 n ((S₁.h + 1) * (S₂.h + 1)) :=
  fun i l => mulUp (PolyZonotope.extG S₁ i (finProdFinEquiv.symm l).1)
    (PolyZonotope.extG S₂ i (finProdFinEquiv.symm l).2)

/-- How far a stored generator can be from the exact product. -/
def PolyZonotope.mulGDiff (S₁ S₂ : PolyZonotope 𝕋 n) :
    Mat 𝕋 n ((S₁.h + 1) * (S₂.h + 1)) :=
  fun i l => subUp (PolyZonotope.mulGUp S₁ S₂ i l) (PolyZonotope.mulGDown S₁ S₂ i l)

/-- The image's exponent column, the two columns added. Over ℕ, so exact. -/
def PolyZonotope.mulE (S₁ S₂ : PolyZonotope 𝕋 n) (hp : S₁.p = S₂.p) :
    Fin S₁.p → Fin ((S₁.h + 1) * (S₂.h + 1)) → ℕ :=
  fun k l => PolyZonotope.extE S₁ k (finProdFinEquiv.symm l).1
      + PolyZonotope.extE S₂ (Fin.cast hp k) (finProdFinEquiv.symm l).2

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
