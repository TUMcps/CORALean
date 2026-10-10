import CORALean.ContSet.PolyZonotope.Float.Operations.BilinE
import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGDown
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

/-!
# `PolyZonotope.bilin`, over a floating-point scalar

The float counterpart of `Real.PolyZonotope.bilin` at a family of bilinear forms `x ↦ y ↦ xᵀ Qₖ y`
(`Real.PolyZonotope.quadBilin`), which is all a bilinear map into `𝕋^m` is. Two polynomial
zonotopes over the *same* factors, `hp` lining their counts up; the result is a polynomial
zonotope again, with the `(h₁+1)(h₂+1)` generators `Gᵢᵀ Q Gⱼ` rounded down, the exponent column the
added one, and the rounding paid into the error box.

Sound only where both operands have an empty independent block and an empty error box, a bilinear
map being no more additive than a quadratic one, so `dependent` comes first at every caller:
`quadMapDep` is this at one set paired with itself, `quadMapMixed` at a product of two.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.bilin (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope 𝕋 n)
    (hp : pZ₁.p = pZ₂.p) : PolyZonotope 𝕋 m where
  p := pZ₁.p
  h := (pZ₁.h + 1) * (pZ₂.h + 1)
  q := 0
  c := fun _ => FloatOps.zero
  G := fun l i => PolyZonotope.bilinGDown Q pZ₁ pZ₂ i l
  E := PolyZonotope.bilinE pZ₁ pZ₂ hp
  GI := Fin.elim0
  err := PolyZonotope.generatorError (PolyZonotope.bilinGDiff Q pZ₁ pZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
