module

public import CORALean.ContSet.Taylm.Real.Definitions.CodeList
public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Operations.Exp
public import CORALean.ContSet.Taylm.Float.Operations.Log
public import CORALean.ContSet.Taylm.Float.Operations.Sin
public import CORALean.ContSet.Taylm.Float.Operations.Cos
public import CORALean.ContSet.Taylm.Float.Operations.Sinh
public import CORALean.ContSet.Taylm.Float.Operations.Cosh

@[expose] public section

/-!
# An intrinsic applied to a float Taylor model

The float layer's share of the source's intrinsics (its Def. 3), for [1, Thm. 3]: `exp`, `log`,
`sin`, `cos`, `sinh` and `cosh`, each under the condition its outer theorem needs, checked in
floats. `exp`, `sinh` and `cosh` need their argument's hull at most `2ᵖ/2`, read as halving it
`p` times and comparing with `1/2`, which is exact; `log` a positive centre and range bottom.
The other intrinsics have no float counterpart here and give `none`, as does a failed check.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.intrinsic (p q s : ℕ) : Real.Taylm.Intrinsic → Taylm 𝕋 n → Option (Taylm 𝕋 n)
  | .exp, T =>
    if Taylm.belowPow p (maximum T.constCoef T.bounds.2) then some (T.exp p) else none
  | .log, T =>
    if ltStrict zero (minimum T.constCoef T.bounds.1) then some (T.log q s) else none
  | .sin, T => some (T.sin p)
  | .cos, T => some (T.cos p)
  | .sinh, T =>
    if Taylm.belowPow p (maximum (absolute T.constCoef)
      (maximum (absolute T.bounds.1) (absolute T.bounds.2))) then some (T.sinh p) else none
  | .cosh, T =>
    if Taylm.belowPow p (maximum (absolute T.constCoef)
      (maximum (absolute T.bounds.1) (absolute T.bounds.2))) then some (T.cosh p) else none
  | _, _ => none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
