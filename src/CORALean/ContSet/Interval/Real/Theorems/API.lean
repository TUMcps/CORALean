import CORALean.ContSet.Interval.Real.Theorems.Convex
import CORALean.ContSet.Interval.Real.Theorems.IsBounded
import CORALean.ContSet.Interval.Real.Theorems.IsClosed
import CORALean.ContSet.Interval.Real.Theorems.IsCompact
import CORALean.ContSet.Interval.Real.Theorems.IsNonempty
import CORALean.ContSet.Interval.Real.Theorems.PlusExact
import CORALean.ContSet.Interval.Real.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Interval.Real.Theorems.MtimesOuter

/-!
# What `Interval` guarantees

An enclosure per operation — `plus` exactly so — and the topological facts a
set-valued integral needs: convex, closed, bounded, and the two last combined
into the compactness an interface field asks for.
-/
