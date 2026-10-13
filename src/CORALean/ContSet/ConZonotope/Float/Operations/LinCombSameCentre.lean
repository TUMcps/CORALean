import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledLeft
import CORALean.ContSet.HPolytope.Float.Operations.HalfScaledRight
import CORALean.ContSet.HPolytope.Float.Operations.Intersection
import CORALean.ContSet.HPolytope.Float.Operations.UnitBox
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# `ConZonotope.linCombSameCentre`: the hull of two sets that share a centre, with nothing rounded

`ConZonotope.linComb` stores the midpoint of the two centres and half their difference, which
round, so its result is only an outer set. Where the two centres are the same vector `c`, the
midpoint is `c` and the half difference is `0`, and the hull is exactly
`c + G₁(λβ₁) + G₂((1 - λ)β₂)`: the generator blocks and the weighted constraint rows of
`linComb` are copied, the centre is `c` and the column of the interpolation parameter is `0`.
Nothing is computed, so nothing rounds, and the error box is the point `0`: what this returns
is exactly the set its stored numbers describe, which an inner approximation needs of it.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The hull of two constrained zonotopes at the centre of the first, exact where it is also the
centre of the second. -/
def ConZonotope.linCombSameCentre (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConZonotope
    𝕋 (Vec 𝕋 n) where
  h := cZ₁.h + cZ₂.h + 1
  c := cZ₁.c
  G := Fin.append (Fin.append cZ₁.G cZ₂.G) fun _ : Fin 1 => fun _ => zero
  P := ((cZ₁.P.intersection (HPolytope.unitBox 𝕋 cZ₁.h)).halfScaledLeft cZ₂.h).intersection
    (HPolytope.halfScaledRight cZ₁.h (cZ₂.P.intersection (HPolytope.unitBox 𝕋 cZ₂.h)))
  E := Interval.point fun _ => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
