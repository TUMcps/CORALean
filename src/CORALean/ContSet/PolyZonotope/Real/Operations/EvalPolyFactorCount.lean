module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly

@[expose] public section

/-!
# `evalPoly` never leaves the shared factor count

Split out of `EvalPoly.lean` (issue #62): read again by the float layer's own
`evalPoly` and by `Theorems/EvalPolyOuter.lean`, both outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The shared factor count `evalPoly` never leaves. -/
theorem PolyZonotope.evalPoly_p (pZ : PolyZonotope (Vec ℝ n)) (coeffs : List (Vec ℝ n)) :
    (pZ.evalPoly coeffs).p = pZ.p := (PolyZonotope.evalPolyP pZ coeffs).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
