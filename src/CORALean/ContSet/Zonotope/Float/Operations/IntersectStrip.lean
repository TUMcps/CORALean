import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Float.Operations.Plus

/-!
# `Zonotope.intersectStrip`, over a floating-point scalar

CORA's `@zonotope/intersectStrip` for a numeric weight matrix `Λ`, as over ℝ: the zonotope
`(I - Λ C) Z ⊕ Λ (y + diag(φ) [-1, 1]^p)`. The matrix `I - Λ C` is rounded into an interval
matrix, `Interval.matMul` of the two stored matrices and one directed subtraction from the
identity, so `Zonotope.mtimesIntervalMat` pays what rounding cost into extra generators and
the error box; the strip part `Λ (y ⊕ diag(φ) [-1, 1]^p)` is `Zonotope.mtimes` of the
box-shaped zonotope. The choice of `Λ` is not modelled, as over ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/intersectStrip` at the weights `Λ`: `(I - Λ C) Z ⊕ Λ (y + diag(φ) [-1, 1]^p)`. -/
def Zonotope.intersectStrip (C : Mat 𝕋 p n) (φ y : Vec 𝕋 p) (Λ : Mat 𝕋 n p)
    (Z : Zonotope 𝕋 n) : Zonotope 𝕋 n :=
  let ΛC : Interval (Mat 𝕋 n n) :=                                  -- Λ C, rounded
    Interval.matMul (Interval.point Λ) (Interval.point C)
  let IM : Interval (Mat 𝕋 n n) :=                                  -- I - Λ C, rounded
    { inf := fun i j => subDown (if i = j then one else zero) (ΛC.sup i j)
      sup := fun i j => subUp (if i = j then one else zero) (ΛC.inf i j) }
  let strip : Zonotope 𝕋 p :=                                       -- y + diag(φ) [-1, 1]^p
    { h := p, c := y, G := fun j i => if i = j then φ i else zero, E := Interval.origin p }
  Zonotope.plus (Zonotope.mtimesIntervalMat IM Z) (Zonotope.mtimes Λ strip)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
