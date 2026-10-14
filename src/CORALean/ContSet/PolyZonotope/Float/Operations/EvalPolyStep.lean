module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.CenterResidual
public import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound
public import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyBoundS
public import CORALean.ContSet.PolyZonotope.Float.Operations.Mul

@[expose] public section

/-!
# One step of Horner's rule, over a floating-point scalar

Split out of `EvalPoly.lean` (issue #62): read again by
`Theorems/EvalPolyOuter.lean`, outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One Horner step: `R` multiplied by `pZ` and shifted by the next coefficient,
the extra uncertainty `R` already carries priced in before `mul`'s own rounding
is added. -/
def PolyZonotope.evalPolyStep (R pZ : PolyZonotope (Vec 𝕋 n)) (hp : R.p = pZ.p) (a0 : Vec 𝕋 n) :
    PolyZonotope (Vec 𝕋 n) where
  p := (PolyZonotope.mul R pZ hp).p
  h := (PolyZonotope.mul R pZ hp).h
  q := (PolyZonotope.mul R pZ hp).q
  c := fun i => addDown ((PolyZonotope.mul R pZ hp).c i) (a0 i)
  G := (PolyZonotope.mul R pZ hp).G
  E := (PolyZonotope.mul R pZ hp).E
  GI := (PolyZonotope.mul R pZ hp).GI
  I_error := ((PolyZonotope.mul R pZ hp).I_error.plus
      (PolyZonotope.centerResidual (PolyZonotope.mul R pZ hp).c a0)).plus
    (Interval.symmetric (fun i =>
      mulUp (PolyZonotope.errorBound R.I_error i) (PolyZonotope.evalPolyBoundS pZ i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
