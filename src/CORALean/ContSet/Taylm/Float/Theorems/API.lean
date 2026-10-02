import CORALean.ContSet.Taylm.Float.Theorems.AbsPolyOfRoundLe
import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.ComposeOuter
import CORALean.ContSet.Taylm.Float.Theorems.ConstOuter
import CORALean.ContSet.Taylm.Float.Theorems.ExpOuter
import CORALean.ContSet.Taylm.Float.Theorems.LogCoefMem
import CORALean.ContSet.Taylm.Float.Theorems.LogOuter
import CORALean.ContSet.Taylm.Float.Theorems.MinusOuter
import CORALean.ContSet.Taylm.Float.Theorems.MtimesOuter
import CORALean.ContSet.Taylm.Float.Theorems.PlusOuter
import CORALean.ContSet.Taylm.Float.Theorems.PolyBoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.PowOuter
import CORALean.ContSet.Taylm.Float.Theorems.SmulOuter
import CORALean.ContSet.Taylm.Float.Theorems.SumOuter
import CORALean.ContSet.Taylm.Float.Theorems.TimesOuter
import CORALean.ContSet.Taylm.Float.Theorems.ToRealTermBounds
import CORALean.ContSet.Taylm.Float.Theorems.UminusOuter
import CORALean.ContSet.Taylm.Float.Theorems.BoundDotLe

/-!
# Float Taylor model guarantees, collected

Each float operation encloses what its exact counterpart does; `abs_polyOf_round_le` is the
one rounding argument they all pay through.
-/
