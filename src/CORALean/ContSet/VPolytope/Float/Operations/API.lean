import CORALean.ContSet.VPolytope.Float.Operations.ColumnGap
import CORALean.ContSet.VPolytope.Float.Operations.Plus
import CORALean.ContSet.VPolytope.Float.Operations.Mtimes
import CORALean.ContSet.VPolytope.Float.Operations.LinComb
import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
import CORALean.ContSet.VPolytope.Float.Operations.And

/-!
# What the float `VPolytope` computes

The same three the exact layer does. `plus` and `mtimes` round every vertex and
charge the gap to the box, which `ColumnGap` is; `linComb` concatenates and
charges nothing.
-/
