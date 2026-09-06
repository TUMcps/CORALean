import CORALean.ContSet.PolyZonotope.Real.Operations.Mul

/-!
# One step of Horner's rule

Split out of `EvalPoly.lean` (issue #62): read again by the float layer's own
`evalPoly` and by `Theorems/EvalPolyOuter.lean` and
`Theorems/EvalPolyExact.lean`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- One Horner step: `R` multiplied by `S`, then shifted by the next
coefficient. Named, `where`-built like `mul` itself, so its fields unfold
directly rather than through a record update's hidden `let`. -/
def PolyZonotope.evalPolyStep (R S : PolyZonotope (Vec ℝ n)) (hp : R.p = S.p) (a0 : Vec ℝ n) :
    PolyZonotope (Vec ℝ n) where
  p := (PolyZonotope.mul R S hp).p
  h := (PolyZonotope.mul R S hp).h
  q := (PolyZonotope.mul R S hp).q
  c := (PolyZonotope.mul R S hp).c + a0
  G := (PolyZonotope.mul R S hp).G
  E := (PolyZonotope.mul R S hp).E
  GI := (PolyZonotope.mul R S hp).GI

end CORALean.Real
