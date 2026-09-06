import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPoly
import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyP

/-!
# `evalPoly` never leaves the shared factor count, over a floating-point scalar

Split out of `EvalPoly.lean` (issue #62): read again by
`Theorems/EvalPolyOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The shared factor count `evalPoly` never leaves. -/
theorem PolyZonotope.evalPoly_p (S : PolyZonotope 𝕋 n) (coeffs : List (Vec 𝕋 n)) :
    (S.evalPoly coeffs).p = S.p := (PolyZonotope.evalPolyP S coeffs).2

end CORALean.Float
