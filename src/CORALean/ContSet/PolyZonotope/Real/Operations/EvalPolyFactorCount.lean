import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly

/-!
# `evalPoly` never leaves the shared factor count

Split out of `EvalPoly.lean` (issue #62): read again by the float layer's own
`evalPoly` and by `Theorems/EvalPolyOuter.lean`, both outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- The shared factor count `evalPoly` never leaves. -/
theorem PolyZonotope.evalPoly_p (S : PolyZonotope (Vec ℝ n)) (coeffs : List (Vec ℝ n)) :
    (S.evalPoly coeffs).p = S.p := (PolyZonotope.evalPolyP S coeffs).2

end CORALean.Real
