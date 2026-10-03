import CORALean.ContSet.Taylm.Real.Definitions.CodeList
import CORALean.ContSet.Taylm.Real.Operations.Exp
import CORALean.ContSet.Taylm.Real.Operations.Log
import CORALean.ContSet.Taylm.Real.Operations.Inv
import CORALean.ContSet.Taylm.Real.Operations.Sqrt
import CORALean.ContSet.Taylm.Real.Operations.InvSqrt
import CORALean.ContSet.Taylm.Real.Operations.Sin
import CORALean.ContSet.Taylm.Real.Operations.Cos
import CORALean.ContSet.Taylm.Real.Operations.Sinh
import CORALean.ContSet.Taylm.Real.Operations.Cosh
import CORALean.ContSet.Taylm.Real.Operations.Asin
import CORALean.ContSet.Taylm.Real.Operations.Acos
import CORALean.ContSet.Taylm.Real.Operations.Atan
import CORALean.ContSet.Taylm.Real.Operations.Tan
import CORALean.ContSet.Taylm.Real.Operations.Tanh
import CORALean.ContSet.Taylm.Real.Operations.Mag

/-!
# An intrinsic applied to a Taylor model

The source's intrinsics (its Def. 3) as [1, Thm. 2]'s code lists call them, each under the
condition the source states for it, read on the model as its own operation's guarantee needs it:
`log`, `sqrt` and `1/sqrt` a positive centre and range bottom, the inverse a hull on one side of
zero, `arcsin` and `arccos` a magnitude below one, `tan` below `π/2`. A model failing its
condition gives `none`, where CORA throws `outOfDomain`: the condition is on the computed model,
not on the function it encloses.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.intrinsic : Taylm.Intrinsic → Taylm n → Option (Taylm n)
  | .exp, T => some T.exp
  | .log, T => if 0 < min T.constCoef T.bounds.1 then some T.log else none
  | .inv, T =>
    if 0 < min T.constCoef T.bounds.1 ∨ max T.constCoef T.bounds.2 < 0 then some T.inv else none
  | .sqrt, T => if 0 < min T.constCoef T.bounds.1 then some T.sqrt else none
  | .invSqrt, T => if 0 < min T.constCoef T.bounds.1 then some T.invSqrt else none
  | .sin, T => some T.sin
  | .cos, T => some T.cos
  | .sinh, T => some T.sinh
  | .cosh, T => some T.cosh
  | .asin, T => if T.mag < 1 then some T.asin else none
  | .acos, T => if T.mag < 1 then some T.acos else none
  | .atan, T => some T.atan
  | .tan, T => if T.mag < Real.pi / 2 then some T.tan else none
  | .tanh, T => some T.tanh

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
