module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadE

@[expose] public section

/-!
# `PolyLevelSet.padVars` over a floating-point scalar

`Real.PolyLevelSet.padVars` at the stored floats: `r` fresh variables in the box `D` that no row
reads, the stored rows and slacks untouched.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same rows over `n + r` variables, the last `r` in `D` and read by none. -/
def PolyLevelSet.padVars (P : PolyLevelSet 𝕋 n) {r : ℕ} (D : Interval (Vec 𝕋 r)) :
    PolyLevelSet 𝕋 (n + r) where
  m := P.m
  q := P.q
  A := P.A
  R := Real.PolyZonotope.padE P.R r
  b := P.b
  b_error := P.b_error
  op := P.op
  dom := P.dom.append D

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
