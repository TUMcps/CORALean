module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `PolyLevelSet.relax` over a floating-point scalar

Each row's slack moved into a variable of its own: row `i` gains the monomial `yᵢ` with
coefficient `b_errorᵢ`, `y` ranging over the box `D`, and the slack left is `zero`. Nothing
rounds, the coefficients being copied, and the rows read back as `Real.PolyLevelSet.relax` by the
slack (`eval_nominalCore_relax`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Row `i` widened by `b_errorᵢ yᵢ`, `yᵢ` a fresh variable in `D` read by that row alone. -/
def PolyLevelSet.relax (P : PolyLevelSet 𝕋 n) (D : Interval (Vec 𝕋 P.m)) :
    PolyLevelSet 𝕋 (n + P.m) where
  m := P.m
  q := P.q + P.m
  A := fun i => Fin.append (P.A i) (diagonalBlock P.b_error i)
  R := Real.PolyZonotope.plusE P.R (Real.PolyZonotope.identE P.m)
  b := P.b
  b_error := fun _ => zero
  op := P.op
  dom := P.dom.append D

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
