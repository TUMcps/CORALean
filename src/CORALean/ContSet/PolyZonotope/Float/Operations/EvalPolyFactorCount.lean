module

public import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPoly
public import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyP

@[expose] public section

/-!
# `evalPoly` never leaves the shared factor count, over a floating-point scalar

Split out of `EvalPoly.lean` (issue #62): read again by
`Theorems/EvalPolyOuter.lean`, outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The shared factor count `evalPoly` never leaves. -/
theorem PolyZonotope.evalPoly_p (pZ : PolyZonotope (Vec 𝕋 n)) (coeffs : List (Vec 𝕋 n)) :
    (pZ.evalPoly coeffs).p = pZ.p := (PolyZonotope.evalPolyP pZ coeffs).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
