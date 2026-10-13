import CORALean.ContSet.PolyZonotope.Real.Operations.Mul

/-!
# One step of Horner's rule

Split out of `EvalPoly.lean` (issue #62): read again by the float layer's own
`evalPoly` and by `Theorems/EvalPolyOuter.lean` and
`Theorems/EvalPolyExact.lean`, all outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One Horner step: `R` multiplied by `pZ`, then shifted by the next
coefficient. Named, `where`-built like `mul` itself, so its fields unfold
directly rather than through a record update's hidden `let`. -/
def PolyZonotope.evalPolyStep (R pZ : PolyZonotope (Vec ℝ n)) (hp : R.p = pZ.p) (a0 : Vec ℝ n) :
    PolyZonotope (Vec ℝ n) where
  p := (PolyZonotope.mul R pZ hp).p
  h := (PolyZonotope.mul R pZ hp).h
  q := (PolyZonotope.mul R pZ hp).q
  c := (PolyZonotope.mul R pZ hp).c + a0
  G := (PolyZonotope.mul R pZ hp).G
  E := (PolyZonotope.mul R pZ hp).E
  GI := (PolyZonotope.mul R pZ hp).GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
