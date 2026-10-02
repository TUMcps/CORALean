import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
import CORALean.ContSet.Taylm.Real.Theorems.ComposeOuter
import CORALean.ContSet.Taylm.Real.Theorems.ConstOuter
import CORALean.ContSet.Taylm.Real.Theorems.ExpOuter
import CORALean.ContSet.Taylm.Real.Theorems.LogOuter
import CORALean.ContSet.Taylm.Real.Theorems.MemConstructIff
import CORALean.ContSet.Taylm.Real.Theorems.MinusOuter
import CORALean.ContSet.Taylm.Real.Theorems.MtimesConstructOuter
import CORALean.ContSet.Taylm.Real.Theorems.MtimesOuter
import CORALean.ContSet.Taylm.Real.Theorems.PlusOuter
import CORALean.ContSet.Taylm.Real.Theorems.PolyBoundsMem
import CORALean.ContSet.Taylm.Real.Theorems.PolyOfFilter
import CORALean.ContSet.Taylm.Real.Theorems.PolyOfMulTerms
import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNeg
import CORALean.ContSet.Taylm.Real.Theorems.PolyOfSmul
import CORALean.ContSet.Taylm.Real.Theorems.PowOuter
import CORALean.ContSet.Taylm.Real.Theorems.SmulOuter
import CORALean.ContSet.Taylm.Real.Theorems.SqrtOuter
import CORALean.ContSet.Taylm.Real.Theorems.SumOuter
import CORALean.ContSet.Taylm.Real.Theorems.TaylorOuter
import CORALean.ContSet.Taylm.Real.Theorems.TermBoundsMem
import CORALean.ContSet.Taylm.Real.Theorems.TimesOuter
import CORALean.ContSet.Taylm.Real.Theorems.UminusOuter
import CORALean.ContSet.Taylm.Real.Theorems.UplusOuter

/-!
# Taylor model guarantees, collected

Each operation encloses the exact function: `Taylm.Encloses` is preserved by the arithmetic,
`bounds_mem` says the range bound holds, and `taylor_outer` is the Lagrange remainder lemma
that `exp_outer`, `log_outer` and `sqrt_outer` instantiate.
-/
