import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Symmetric
import CORALean.ContSet.PolyZonotope.Float.Operations.CenterResidual
import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound
import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyBoundS
import CORALean.ContSet.PolyZonotope.Float.Operations.Mul

/-!
# One step of Horner's rule, over a floating-point scalar

Split out of `EvalPoly.lean` (issue #62): read again by
`Theorems/EvalPolyOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- One Horner step: `R` multiplied by `S` and shifted by the next coefficient,
the extra uncertainty `R` already carries priced in before `mul`'s own rounding
is added. -/
def PolyZonotope.evalPolyStep (R S : PolyZonotope 𝕋 n) (hp : R.p = S.p) (a0 : Vec 𝕋 n) :
    PolyZonotope 𝕋 n where
  p := (PolyZonotope.mul R S hp).p
  h := (PolyZonotope.mul R S hp).h
  q := (PolyZonotope.mul R S hp).q
  c := fun i => addDown ((PolyZonotope.mul R S hp).c i) (a0 i)
  G := (PolyZonotope.mul R S hp).G
  E := (PolyZonotope.mul R S hp).E
  GI := (PolyZonotope.mul R S hp).GI
  err := ((PolyZonotope.mul R S hp).err.plus
      (PolyZonotope.centerResidual (PolyZonotope.mul R S hp).c a0)).plus
    (Interval.symmetric (fun i =>
      mulUp (PolyZonotope.errorBound R.err i) (PolyZonotope.evalPolyBoundS S i)))

end CORALean.Float
